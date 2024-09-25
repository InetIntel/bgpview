/* This source code is Copyright (c) 2023 Georgia Tech Research Corporation. All
 * Rights Reserved. Permission to copy, modify, and distribute this software and
 * its documentation for academic research and education purposes, without fee,
 * and without a written agreement is hereby granted, provided that the above
 * copyright notice, this paragraph and the following three paragraphs appear in
 * all copies. Permission to make use of this software for other than academic
 * research and education purposes may be obtained by contacting:
 *
 *  Office of Technology Licensing
 *  Georgia Institute of Technology
 *  926 Dalney Street, NW
 *  Atlanta, GA 30318
 *  404.385.8066
 *  techlicensing@gtrc.gatech.edu
 *
 * This software program and documentation are copyrighted by Georgia Tech
 * Research Corporation (GTRC). The software program and documentation are 
 * supplied "as is", without any accompanying services from GTRC. GTRC does
 * not warrant that the operation of the program will be uninterrupted or
 * error-free. The end-user understands that the program was developed for
 * research purposes and is advised not to rely exclusively on the program for
 * any reason.
 *
 * IN NO EVENT SHALL GEORGIA TECH RESEARCH CORPORATION BE LIABLE TO ANY PARTY
 * FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES,
 * INCLUDING
 * LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION,
 * EVEN IF GEORGIA TECH RESEARCH CORPORATION HAS BEEN ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE. GEORGIA TECH RESEARCH CORPORATION SPECIFICALLY DISCLAIMS ANY
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED
 * HEREUNDER IS ON AN "AS IS" BASIS, AND  GEORGIA TECH RESEARCH CORPORATION HAS
 * NO OBLIGATIONS TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
 * MODIFICATIONS.
 *
 * This source code is part of the bgpview software. The original bgpview
 * software is Copyright (c) 2014 The Regents of the University of California.
 * All rights reserved. Permission to copy, modify, and distribute this
 * software for academic research and education purposes is subject to the
 * conditions and copyright notices in the source code files and in the
 * included LICENSE file.
 */

/*
 * Copyright (C) 2014 The Regents of the University of California.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#include "bvc_pergeovisibility_ipinfo.h"
#include "bgpview_consumer_interface.h"
#include "bgpstream_utils_patricia.h"
#include "bgpstream_utils_pfx_set.h"
#include "khash.h"
#include "utils.h"
#include "libipmeta.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>
#include <errno.h>

#define NAME "per-geo-visibility-ipinfo"
#define METRIC_PREFIX "prefix-visibility"

#define METRIC_PATH_NETACQ_EDGE_CONTINENT "geo.ipinfo"

#define METRIC_PATH_NETACQ_EDGE_COUNTRY "geo.ipinfo"

#define METRIC_PATH_NETACQ_EDGE_POLYS "geo.ipinfo"

#define METRIC_PATH_GEOASN_COUNTRY "geoasn.ipinfo.country"
#define METRIC_PATH_GEOASN_REGION "geoasn.ipinfo.region"

#define METRIC_THRESH_FORMAT "v%d.visibility_threshold.%s.%s"

#define META_METRIC_PREFIX_FORMAT "%s.meta.bgpview.consumer." NAME ".%s"

#define BUFFER_LEN 1024
#define MAX_NUM_PEERS 1024
#define MAX_IP_VERSION_ALLOWED BGPSTREAM_MAX_IP_VERSION_IDX

static const char *continent_strings[] = {
  "??", // Unknown
  "AF", // Africa
  "AN", // Antarctica
  "AS", // Asia
  "EU", // Europe
  "NA", // North America
  "OC", // Oceania
  "SA", // South Africa
};

/* mapping from netacuity continent code to our string array */
static const int netacq_cont_map[] = {
  0, // 0: '**' => '??'
  1, // 1: 'af' => 'AF'
  2, // 2: 'an' => 'AN'
  6, // 3: 'au' => 'OC'
  3, // 4: 'as' => 'AS'
  4, // 5: 'eu' => 'EU'
  5, // 6: 'na' => 'NA'
  7, // 7: 'sa' => 'SA'
};

/** The max country code value (currently the actual max is 30,404, but this
 * could easily go higher. be careful) */
#define METRIC_ISO2_ASCII_MAX UINT16_MAX

/** XXX this could grow -- at time of writing, the max code is 4893 but
 *  we may add regions to IODA in the future...
 */
#define METRIC_REGIONID_MAX 5000


/** Convert a 2 char byte array to a 16 bit number */
#define CC_16(bytes) ((bytes[0] << 8) | bytes[1])

/** a hash type to map ISO3 country codes to a continent.ISO2 string */
KHASH_INIT(strstr, char *, char *, 1, kh_str_hash_func, kh_str_hash_equal)

/** Define our own hash function that doesn't consider a /24's (empty) least
 * significant byte.  We simply right-shift the unused host bits away and
 * multiply the result by the prime number 59, to distribute our keys more
 * uniformly across the hash table's buckets. */
#define kh_slash24_hash_func(key)   (khint32_t) (((key) >> 8) * 59)
#define kh_slash24_hash_equal(a, b) ((a) == (b))

KHASH_INIT(slash24_id_set /* name */, uint32_t /* khkey_t */,
           char /* khval_t */, 0 /* kh_is_set */,
           kh_slash24_hash_func /*__hash_func */,
           kh_slash24_hash_equal /* __hash_equal */)



/* We define our own set data structure because we need a different hash
 * function for dealing with our /24s.
 */
typedef struct slash24_id_set {
  khash_t(slash24_id_set) * hash;
} slash24_id_set_t;

/* creates a metric:
 * [CHAIN_STATE->metric_prefix].prefix-visibility.[geopfx].[geofmt]
 */
#define METRIC_PREFIX_INIT(target, geopfx, geostr)                             \
  do {                                                                         \
    char key_buffer[BUFFER_LEN];                                               \
    snprintf(key_buffer, BUFFER_LEN, "%s." METRIC_PREFIX "." geopfx ".%s",     \
             CHAIN_STATE->metric_prefix, geostr);                              \
    if ((target = per_geo_init(consumer, key_buffer)) == NULL) {               \
      goto err;                                                                \
    }                                                                          \
  } while (0)

#define METRIC_KEY_INIT(idx, metric_pfx, ipv, thresh, leaf)                    \
  do {                                                                         \
    char key_buffer[BUFFER_LEN];                                               \
    snprintf(key_buffer, BUFFER_LEN, "%s." METRIC_THRESH_FORMAT, metric_pfx,   \
             ipv, thresh, leaf);                                               \
    idx = timeseries_kp_add_key(STATE->kp, key_buffer);                        \
  } while (0)

/* Hides the ugly reallocation code that allocates more space for our IP address
 * runs.
 */
#define ADD_ADDR_RUN(runs, num_runs, size, run_struct_size, run_cnt_size)                                     \
  do {                                                                         \
    if (((runs) = realloc((runs), run_struct_size *                            \
                                  ((size) + 1))) == NULL) {                    \
      return -1;                                                               \
    }                                                                          \
    (runs)[(size)] = NULL;                                                     \
    if (((num_runs) = realloc((num_runs), run_cnt_size *                       \
                                          ((size) + 1))) == NULL) {            \
      return -1;                                                               \
    }                                                                          \
    (num_runs)[(size)] = 0;                                                    \
  } while (0)                                                                  \


#define ADD_V6_PFX_SET(sets, size) \
  do { \
    if (((sets) = realloc((sets), \
            sizeof(bgpstream_ipv6_pfx_set_t *) * ((size) + 1))) == NULL) { \
      return -1; \
    } \
    (sets)[(size)] = bgpstream_ipv6_pfx_set_create(); \
  } while (0);

#define STATE (BVC_GET_STATE(consumer, pergeovisibility))

#define CHAIN_STATE (BVC_GET_CHAIN_STATE(consumer))

/* our 'class' */
static bvc_t bvc_pergeovisibility_ipinfo = {
  BVC_ID_PERGEOVISIBILITY_IPINFO,            // ID
  NAME,                                      // Name
  BVC_GENERATE_PTRS(pergeovisibility_ipinfo) // Generate function pointers
};

/* Visibility Thresholds indexes */
typedef enum {
  VIS_1_FF_ASN = 0,
  VIS_25_PERCENT = 1,
  VIS_50_PERCENT = 2,
  VIS_75_PERCENT = 3,
  VIS_100_PERCENT = 4,
} vis_thresholds_t;

static double threshold_vals[] = {
  0,    // VIS_1_FF_ASN
  0.25, // VIS_25_PERCENT
  0.5,  // VIS_50_PERCENT
  0.75, // VIS_75_PERCENT
  1,    // VIS_100_PERCENT
};

#define VIS_THRESHOLDS_CNT ARR_CNT(threshold_vals)

static const char *threshold_strings[] = {
  "min_1_ff_peer_asn",     // VIS_1_FF_ASN
  "min_25%_ff_peer_asns",  // VIS_25_PERCENT
  "min_50%_ff_peer_asns",  // VIS_50_PERCENT
  "min_75%_ff_peer_asns",  // VIS_75_PERCENT
  "min_100%_ff_peer_asns", // VIS_100_PERCENT
};

/* Run-length encoding for a set of subsequent IP addresses.  We use this data
 * structure to determine the number of /24s geolocated to a continent, country,
 * or region.
 */
typedef struct ip_addr_run {

  /* The network address serving as the point of reference for our run. */
  uint64_t network_addr;

  /* The number of subsequent IP addresses (or /64s for a v6 run) */
  uint64_t num_ips;

} ip_addr_run_t;

typedef struct ip_addr_run_set {
    ip_addr_run_t *runs;
    uint64_t run_cnt;
} ip_addr_run_set_t;

typedef struct per_thresh {

  /* All the prefixes that belong to this threshold, i.e. they have been
   * observed by at least THRESHOLD full feed ASNs, but they do not belong to a
   * higher threshold
   */
  bgpstream_patricia_tree_t *pfxs;

  /* All the ASNs that announce a prefix in this geographical region */
  bgpstream_id_set_t *asns;

  /* All the ASNs that announce a v6 prefix in this geographical region */
  bgpstream_id_set_t *asns_v6;

  /* All the /24s (their network address, to be precise) that geolocate to this
   * geographical region
   */
  slash24_id_set_t *slash24s;


  bgpstream_patricia_tree_t *v6_subnets;

  int32_t pfx_cnt_idx[BGPSTREAM_MAX_IP_VERSION_IDX];
  int32_t subnet_cnt_idx[BGPSTREAM_MAX_IP_VERSION_IDX];
  int32_t asns_cnt_idx[BGPSTREAM_MAX_IP_VERSION_IDX];

  /* TODO: other infos here ? */

} __attribute__((packed)) per_thresh_t;

/** pergeo_info_t
 *  network visibility information related to a single geographical location
 *  (continent, country, region, polygon)
 */
typedef struct per_geo {

  per_thresh_t thresholds[VIS_THRESHOLDS_CNT];

} __attribute__((packed)) per_geo_t;

KHASH_MAP_INIT_INT64(geo_as_run, ip_addr_run_set_t *)
KHASH_MAP_INIT_INT64(geo_as, per_geo_t *)

/** Attached to prefixes in the view to cache continent, country, region, and
 * polygon indices.
 */
typedef struct perpfx_cache {

  /** Continents this prefix is in. (Index into the STATE->continents array) */
  uint16_t *continent_idxs;
  /** Number of continents in the array */
  uint8_t continent_idxs_cnt;
  /** IP address runs geolocated to the given continents */
  ip_addr_run_t **continent_addr_runs;
  bgpstream_ipv6_pfx_set_t **continent_addr6_pfxs;
  /* Number of IP address runs geolocated to the given continents.  This is
   * *not* the length of continent_addr_runs; that is determined by
   * continent_idxs_cnt.
   */
  uint64_t *per_continent_addr_run_cnt;
  uint64_t *per_continent_addr6_pfx_cnt;

  /** Countries this prefix is in. (Index into the STATE->countries array) */
  uint16_t *country_idxs;
  /** Number of countries in the array */
  uint8_t country_idxs_cnt;
  /** IP address runs geolocated to the given countries */
  ip_addr_run_t **country_addr_runs;
  bgpstream_ipv6_pfx_set_t **country_addr6_pfxs;
  /* Number of IP address runs geolocated to the given countries.  This is
   * *not* the length of country_addr_runs; that is determined by
   * country_idxs_cnt.
   */
  uint64_t *per_country_addr_run_cnt;
  uint64_t *per_country_addr6_pfx_cnt;

  kh_geo_as_run_t *country_as_addr_runs;
  kh_geo_as_run_t *region_as_addr_runs;

  /** Regions that this prefix belongs to */
  uint16_t *poly_table_idxs;
  /** Number of regions */
  uint16_t poly_table_idxs_cnt;
  /** IP address runs geolocated to the given regions */
  ip_addr_run_t **poly_addr_runs;
  bgpstream_ipv6_pfx_set_t **poly_addr6_pfxs;
  /* Number of IP address runs geolocated to the given region.  This is *not*
   * the length of poly_addr_runs; that is determined by poly_table_idxs_cnt.
   */
  uint64_t *per_poly_addr_run_cnt;
  uint64_t *per_poly_addr6_pfx_cnt;

} __attribute__((packed)) perpfx_cache_t;

/* our 'instance' */
typedef struct bvc_pergeovisibility_state {

  /** ipmeta structures */
  char *provider_config;
  char *provider_name;
  char *provider_arg;
  int reload_freq;
  uint32_t last_reload;
  ipmeta_t *ipmeta;
  ipmeta_provider_t *provider;
  ipmeta_record_set_t *records;

  char *regions_csv_file;
  char *geoasn_csv_file;

  /** Array indexed by continent code */
  per_geo_t *continents[METRIC_ISO2_ASCII_MAX];

  /** Array indexed by country code */
  per_geo_t *countries[METRIC_ISO2_ASCII_MAX];

  /** Array of region IDs (specific to IODA) */
  per_geo_t **polygons;

  kh_geo_as_t *geoasn_countries;
  kh_geo_as_t *geoasn_regions;

  /** Array of table sizes */
  int polygons_cnt;

  /** Re-usable variables that are used in the flip table
   *  function: we make them part of the state to avoid
   *  allocating new memory each time we process a new
   *  view */
  bgpstream_id_set_t *ff_asns;
  uint32_t origin_asns[MAX_NUM_PEERS];
  uint16_t valid_origins;

  /** Timeseries Key Package */
  timeseries_kp_t *kp;

  /* META metric values */
  int arrival_delay_idx;
  int processed_delay_idx;
  int processing_time_idx;

} bvc_pergeovisibility_state_t;

/* ==================== PARSE ARGS FUNCTIONS ==================== */

/** Print usage information to stderr */
static void usage(bvc_t *consumer)
{
  fprintf(stderr, "consumer usage: %s -p <ipmeta-provider> -R <region file>\n", consumer->name);
}

/** Parse the arguments given to the consumer */
static int parse_args(bvc_t *consumer, int argc, char **argv)
{
  int opt;
  assert(argc > 0 && argv != NULL);

  /* NB: remember to reset optind to 1 before using getopt! */
  optind = 1;

  /* remember the argv strings DO NOT belong to us */
  while ((opt = getopt(argc, argv, ":p:r:G:R:?")) >= 0) {
    switch (opt) {
    case 'p':
      STATE->provider_config = strdup(optarg);
      assert(STATE->provider_config != NULL);
      break;
    case 'r':
      STATE->reload_freq = atoi(optarg);
      break;
    case 'R':
      STATE->regions_csv_file = strdup(optarg);
      assert(STATE->regions_csv_file != NULL);
      break;
    case 'G':
      STATE->geoasn_csv_file = strdup(optarg);
      assert(STATE->geoasn_csv_file != NULL);
      break;

    case '?':
    case ':':
    default:
      usage(consumer);
      return -1;
    }
  }

  /* ipmeta provider is required */
  if (STATE->provider_config == NULL) {
    fprintf(stderr,
            "ERROR: geolocation provider must be configured using -p\n");
    usage(consumer);
    return -1;
  }

  if (STATE->regions_csv_file == NULL) {
    fprintf(stderr,
            "ERROR: regions file must be provided using -R\n");
    usage(consumer);
    return -1;
  }

  return 0;
}

/* ==================== ORIGINS FUNCTIONS ==================== */

/* check if an origin ASN is already part of the array and
 * if not it adds it */
static void add_origin(bvc_pergeovisibility_state_t *state,
                       bgpstream_as_path_seg_t *origin_seg)
{
  uint32_t origin_asn;
  int i;

  if (origin_seg == NULL || origin_seg->type != BGPSTREAM_AS_PATH_SEG_ASN) {
    return;
  }
  origin_asn = ((bgpstream_as_path_seg_asn_t *)origin_seg)->asn;

  /* we do a linear search since the number of distinct origins should be very
     small (often just 1) */
  for (i = 0; i < state->valid_origins; i++) {
    if (state->origin_asns[i] == origin_asn) {
      /* origin_asn is already there */
      return;
    }
  }
  /* if we did not find the origin, we add it*/
  state->origin_asns[state->valid_origins++] = origin_asn;
}

/* ==================== SET FUNCTIONS ==================== */

static int slash24_id_set_insert(slash24_id_set_t *set, uint32_t id)
{
  int khret;

  kh_put(slash24_id_set, set->hash, id, &khret);
  return khret;
}

static slash24_id_set_t *slash24_id_set_create(void)
{
  slash24_id_set_t *set;

  if ((set = (slash24_id_set_t *) malloc(sizeof(slash24_id_set_t))) == NULL) {
    return NULL;
  }

  if ((set->hash = kh_init(slash24_id_set)) == NULL) {
    kh_destroy(slash24_id_set, set->hash);
    free(set);
    return NULL;
  }
  /* Pre-allocate to reduce the number of expensive realloc calls. The minimum
   * number that kh_resize accepts is 4. */
  kh_resize(slash24_id_set, set->hash, 4);

  return set;
}

static int slash24_id_set_merge(slash24_id_set_t *dst_set,
                                slash24_id_set_t *src_set)
{
  khiter_t k;
  for (k = kh_begin(src_set->hash); k != kh_end(src_set->hash); ++k) {
    if (kh_exist(src_set->hash, k)) {
      if (slash24_id_set_insert(dst_set, kh_key(src_set->hash, k)) < 0) {
        return -1;
      }
    }
  }

  return 0;
}

static void slash24_id_set_clear(slash24_id_set_t *set)
{
  kh_clear(slash24_id_set, set->hash);
}

static int slash24_id_set_size(slash24_id_set_t *set)
{
  return kh_size(set->hash);
}

static void slash24_id_set_destroy(slash24_id_set_t *set)
{
  kh_destroy(slash24_id_set, set->hash);
  free(set);
}

/* ==================== PER-GEO-INFO FUNCTIONS ==================== */

static bgpstream_ipv6_pfx_set_t *update_ip6_prefix(
                bgpstream_ipv6_pfx_set_t *geo_pfxs,
                uint64_t cur_address, uint64_t num_slash64s) {

  uint64_t zero = 0;
  bgpstream_pfx_t newpfx;

  /* Convert into a usable prefix */
  if (num_slash64s == 0) {
    newpfx.mask_len = 64;
  } else {
    newpfx.mask_len = 64 - log2(num_slash64s);
  }
  newpfx.allowed_matches = BGPSTREAM_PREFIX_MATCH_ANY;
  newpfx.address.version = BGPSTREAM_ADDR_VERSION_IPV6;

  newpfx.bs_ipv6.mask_len = newpfx.mask_len;
  newpfx.bs_ipv6.address.version = BGPSTREAM_ADDR_VERSION_IPV6;
  memset(newpfx.bs_ipv6.address.addr.s6_addr, 0, 16);
  newpfx.bs_ipv6.address.addr.s6_addr[0] = cur_address >> 56;
  newpfx.bs_ipv6.address.addr.s6_addr[1] = (cur_address >> 48) & 0xFF;
  newpfx.bs_ipv6.address.addr.s6_addr[2] = (cur_address >> 40) & 0xFF;
  newpfx.bs_ipv6.address.addr.s6_addr[3] = (cur_address >> 32) & 0xFF;
  newpfx.bs_ipv6.address.addr.s6_addr[4] = (cur_address >> 24) & 0xFF;
  newpfx.bs_ipv6.address.addr.s6_addr[5] = (cur_address >> 16) & 0xFF;
  newpfx.bs_ipv6.address.addr.s6_addr[6] = (cur_address >> 8) & 0xFF;
  newpfx.bs_ipv6.address.addr.s6_addr[7] = (cur_address & 0xFF);

  /* Use bgpstream_ipv6_pfx_set_insert() to add to the prefix set */
  bgpstream_ipv6_pfx_set_insert(geo_pfxs, &(newpfx.bs_ipv6));

  return geo_pfxs;

}

static ip_addr_run_t *update_ip_addr_run(ip_addr_run_t *addr_runs,
                                         uint64_t *num_runs,
                                         uint64_t cur_address,
                                         uint64_t num_ips)
{
  ip_addr_run_t *run = NULL;

  /* If the given addr_runs has not been allocated yet, we are dealing with a
   * new location.  In this case, we allocate storage, populate it with our
   * genesis address, and return a pointer to the newly-allocated storage.
   */
  if (addr_runs == NULL) {
    if ((addr_runs = malloc(sizeof(ip_addr_run_t))) == NULL) {
      return NULL;
    }
    (*num_runs)++;

    run = addr_runs;
    run->network_addr = cur_address;
    run->num_ips = num_ips;

    return addr_runs;
  }

  run = &(addr_runs[(*num_runs) - 1]);
  assert(run->network_addr != cur_address);

  /* We are dealing with a continuation of a past run.  All we need to do is add
   * the number of new IP addresses to the past run.
   */
  if (cur_address == (run->network_addr + run->num_ips)) {
    run->num_ips += num_ips;

  /* We are dealing with a new run for a country that already has runs.  We have
   * to add a new ip_addr_run_t data structure and populate it.
   */
  } else {
    if ((addr_runs = realloc(addr_runs, sizeof(ip_addr_run_t) *
                                               ((*num_runs) + 1))) == NULL) {
      return NULL;
    }
    (*num_runs)++;

    run = &(addr_runs[(*num_runs) - 1]);
    run->network_addr = cur_address;
    run->num_ips = num_ips;
  }

  return addr_runs;
}

static int per_thresh_init(bvc_t *consumer, per_thresh_t *pt,
                           const char *metric_pfx, const char *thresh_str)
{
  int v;

  /* create Patricia Tree */
  if ((pt->pfxs = bgpstream_patricia_tree_create(NULL)) == NULL) {
    goto err;
  }

  /* create ASN set  */
  if ((pt->asns = bgpstream_id_set_create()) == NULL) {
    goto err;
  }

  if ((pt->asns_v6 = bgpstream_id_set_create()) == NULL) {
    goto err;
  }

  /* create /24 set */
  if ((pt->slash24s = slash24_id_set_create()) == NULL) {
    goto err;
  }

  if ((pt->v6_subnets = bgpstream_patricia_tree_create(NULL)) == NULL) {
    goto err;
  }

  /* create indexes for timeseries */
  for (v = 0; v < MAX_IP_VERSION_ALLOWED; v++) {
    /* visible_prefixes_cnt */
    METRIC_KEY_INIT(pt->pfx_cnt_idx[v], metric_pfx, bgpstream_idx2number(v),
                    thresh_str, "visible_prefixes_cnt");

    /* visible_ips_cnt */
    METRIC_KEY_INIT(pt->subnet_cnt_idx[v], metric_pfx, bgpstream_idx2number(v),
                    thresh_str,
                    v == bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4)
                      ? "visible_slash24_cnt"
                      : "visible_slash64_cnt");

    /* visible_asns_cnt */
    METRIC_KEY_INIT(pt->asns_cnt_idx[v], metric_pfx, bgpstream_idx2number(v),
                    thresh_str, "visible_asns_cnt");
  }

  return 0;

err:
  return -1;
}

static per_geo_t *per_geo_init(bvc_t *consumer, const char *metric_pfx)
{
  int i;

  per_geo_t *pg = NULL;

  if ((pg = malloc_zero(sizeof(per_geo_t))) == NULL) {
    return NULL;
  }

  for (i = 0; i < VIS_THRESHOLDS_CNT; i++) {
    if (per_thresh_init(consumer, &pg->thresholds[i], metric_pfx,
                        threshold_strings[i]) != 0) {
      return NULL;
    }
  }

  return pg;
}

static void add_geo_v6pfx_to_tree(bgpstream_pfx_t *pfx, void *userdata)
{

  per_thresh_t *pt = (per_thresh_t *)userdata;
  bgpstream_patricia_tree_insert(pt->v6_subnets, pfx);
}

static int per_geo_update_v6(bvc_t *consumer, per_geo_t *pg,
                bgpstream_pfx_t *pfx, bgpstream_ipv6_pfx_set_t *pfx_set) {

  uint32_t num_slash24s, offset = 0;
  /* number of full feed ASNs for the current IP version*/
  int totalfullfeed =
    CHAIN_STATE
      ->full_feed_peer_asns_cnt[bgpstream_ipv2idx(pfx->address.version)];
  assert(totalfullfeed > 0);

  /* number of full feed ASNs observing the current prefix*/
  int pfx_ff_cnt = bgpstream_id_set_size(STATE->ff_asns);
  assert(pfx_ff_cnt > 0);

  double ratio = (double)pfx_ff_cnt / (double)totalfullfeed;

  /* we navigate the thresholds array starting from the
   * higher one, and populate each threshold information
   * only if the prefix belongs there */
  int i, j, k;
  for (i = VIS_THRESHOLDS_CNT - 1; i >= 0; i--) {
    if (ratio >= threshold_vals[i]) {
      /* add prefix to the Patricia Tree */
      if (bgpstream_patricia_tree_insert(pg->thresholds[i].pfxs, pfx) == NULL) {
        return -1;
      }
      /* add origin ASNs to asns set */
      for (j = 0; j < STATE->valid_origins; j++) {

        bgpstream_id_set_insert(pg->thresholds[i].asns_v6,
              STATE->origin_asns[j]);
      }

      if (bgpstream_ipv6_pfx_set_iterate(pfx_set, add_geo_v6pfx_to_tree,
              (void *) &(pg->thresholds[i])) < 0) {
        return -1;
      }
      break;
    }
  }
  return 0;
}

static int per_geo_update(bvc_t *consumer, per_geo_t *pg, bgpstream_pfx_t *pfx,
                          ip_addr_run_t *runs, uint64_t num_runs, int index)
{
  uint32_t num_slash24s, offset = 0;
  /* number of full feed ASNs for the current IP version*/
  int totalfullfeed =
    CHAIN_STATE
      ->full_feed_peer_asns_cnt[bgpstream_ipv2idx(pfx->address.version)];
  assert(totalfullfeed > 0);

  /* number of full feed ASNs observing the current prefix*/
  int pfx_ff_cnt = bgpstream_id_set_size(STATE->ff_asns);
  assert(pfx_ff_cnt > 0);

  double ratio = (double)pfx_ff_cnt / (double)totalfullfeed;

  /* we navigate the thresholds array starting from the
   * higher one, and populate each threshold information
   * only if the prefix belongs there */
  int i, j, k;
  for (i = VIS_THRESHOLDS_CNT - 1; i >= 0; i--) {
    if (ratio >= threshold_vals[i]) {
      /* add prefix to the Patricia Tree */
      if (bgpstream_patricia_tree_insert(pg->thresholds[i].pfxs, pfx) == NULL) {
        return -1;
      }
      /* add origin ASNs to asns set */
      for (j = 0; j < STATE->valid_origins; j++) {

        bgpstream_id_set_insert(pg->thresholds[i].asns,
              STATE->origin_asns[j]);
      }
      /* "Explode" each run into a series of /24 or /64 networks and add them
       * to the set.
       */
      for (j = 0; j < num_runs; j++) {
        /* Determine the offset to the beginning of the /24. */
        offset = runs[j].network_addr & 0x000000ff;
        /* Round up to the next-highest number of /24 */
        num_slash24s = (runs[j].num_ips + offset + 255) / 256;

        for (k = 0; k < num_slash24s; k++) {
          slash24_id_set_insert(pg->thresholds[i].slash24s,
                                (runs[j].network_addr & 0xffffff00) + (k << 8));
        }
      }
      break;
    }
  }
  return 0;
}

static void per_geo_destroy(per_geo_t *pg)
{
  int i;
  for (i = 0; i < VIS_THRESHOLDS_CNT; i++) {
    bgpstream_patricia_tree_destroy(pg->thresholds[i].pfxs);
    bgpstream_id_set_destroy(pg->thresholds[i].asns);
    bgpstream_id_set_destroy(pg->thresholds[i].asns_v6);
    slash24_id_set_destroy(pg->thresholds[i].slash24s);
    bgpstream_patricia_tree_destroy(pg->thresholds[i].v6_subnets);
  }
  free(pg);
}

/* ==================== UTILITY FUNCTIONS ==================== */

static uint64_t first_pfx_addr(bgpstream_pfx_t *pfx) {

  if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
    return ntohl(pfx->address.bs_ipv4.addr.s_addr);
  } else {
    uint64_t addr = 0;

    addr += (((uint64_t)pfx->address.bs_ipv6.addr.s6_addr[0]) << 56);
    addr += (((uint64_t)pfx->address.bs_ipv6.addr.s6_addr[1]) << 48);
    addr += (((uint64_t)pfx->address.bs_ipv6.addr.s6_addr[2]) << 40);
    addr += (((uint64_t)pfx->address.bs_ipv6.addr.s6_addr[3]) << 32);
    addr += (((uint64_t)pfx->address.bs_ipv6.addr.s6_addr[4]) << 24);
    addr += (((uint64_t)pfx->address.bs_ipv6.addr.s6_addr[5]) << 16);
    addr += (((uint64_t)pfx->address.bs_ipv6.addr.s6_addr[6]) << 8);
    addr += (((uint64_t)pfx->address.bs_ipv6.addr.s6_addr[7]));
    return addr;
  }
}

static uint64_t last_pfx_addr(bgpstream_pfx_t *pfx) {

  uint64_t first_addr = first_pfx_addr(pfx);

  if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
    /* Return the last IPv4 address of the prefix. */
    return first_addr + (1 << (32 - pfx->mask_len)) - 1;
  }

  /* I'm assuming the prefix is IPv6 if we get here */
  if (pfx->mask_len >= 64) {
    return first_addr;
  }

  return first_addr + (1UL << 64 - (pfx->mask_len)) - 1;
}

static int init_kp(bvc_t *consumer)
{
  /* init key package and meta metrics */
  if ((STATE->kp = timeseries_kp_init(BVC_GET_TIMESERIES(consumer), 1)) ==
      NULL) {
    fprintf(stderr, "Error: Could not create timeseries key package\n");
    return -1;
  }

  char buffer[BUFFER_LEN];
  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "arrival_delay");
  if ((STATE->arrival_delay_idx = timeseries_kp_add_key(STATE->kp, buffer)) ==
      -1) {
    return -1;
  }
  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "processed_delay");
  if ((STATE->processed_delay_idx = timeseries_kp_add_key(STATE->kp, buffer)) ==
      -1) {
    return -1;
  }
  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "processing_time");
  if ((STATE->processing_time_idx = timeseries_kp_add_key(STATE->kp, buffer)) ==
      -1) {
    return -1;
  }

  return 0;
}

static int init_ipmeta(bvc_t *consumer)
{
  /* initialize ipmeta structure */
  if ((STATE->ipmeta = ipmeta_init(IPMETA_DS_PATRICIA)) == NULL) {
    fprintf(stderr, "Error: Could not initialize ipmeta \n");
    return -1;
  }

  if (STATE->provider_name == NULL) {
    /* need to parse the string given by the user */
    assert(STATE->provider_arg == NULL);
    STATE->provider_name = STATE->provider_config;

    /* the string at STATE->provider_config will contain the name of the plugin,
       optionally followed by a space and then the arguments to pass to the
       plugin */
    if ((STATE->provider_arg = strchr(STATE->provider_config, ' ')) != NULL) {
      /* set the space to a nul, which allows STATE->provider_configs[i] to be
         used for the provider name, and then increment plugin_arg_ptr to point
         to
         the next character, which will be the start of the arg string (or at
         worst case, the terminating \0 */
      *STATE->provider_arg = '\0';
      STATE->provider_arg++;
    }
  }

  /* lookup the provider using the name given  */
  if ((STATE->provider = ipmeta_get_provider_by_name(
         STATE->ipmeta, STATE->provider_name)) == NULL) {
    fprintf(stderr, "ERROR: Invalid provider name: %s\n", STATE->provider_name);
    return -1;
  }

  /* for now we only support the netacq-edge provider */
  if (ipmeta_get_provider_id(STATE->provider) != IPMETA_PROVIDER_IPINFO) {
    fprintf(stderr,
            "ERROR: Only the IPInfo provider is currently supported\n");
  }

  if (ipmeta_enable_provider(STATE->ipmeta, STATE->provider,
                             STATE->provider_arg) != 0) {
    fprintf(stderr, "ERROR: Could not enable provider %s\n",
            STATE->provider_config);
    return -1;
  }

  /* initialize a (reusable) record set structure  */
  if ((STATE->records = ipmeta_record_set_init()) == NULL) {
    fprintf(stderr, "ERROR: Could not init record set\n");
    return -1;
  }

  return 0;
}

static void destroy_ipmeta(bvc_t *consumer)
{
  int i, j;
  khiter_t k;
  per_geo_t *pg;

  for (i = 0; i < METRIC_ISO2_ASCII_MAX; i++) {
    /* continents */
    if (STATE->continents != NULL && STATE->continents[i] != NULL) {
      per_geo_destroy(STATE->continents[i]);
      STATE->continents[i] = NULL;
    }

    /* countries */
    if (STATE->countries != NULL && STATE->countries[i] != NULL) {
      per_geo_destroy(STATE->countries[i]);
      STATE->countries[i] = NULL;
    }
  }

  for (j = 0; j < STATE->polygons_cnt; j++) {
    if (STATE->polygons != NULL && STATE->polygons[j] != NULL) {
      per_geo_destroy(STATE->polygons[j]);
      STATE->polygons[j] = NULL;
    }
  }
  STATE->polygons_cnt = 0;

  if (STATE->geoasn_countries) {
    for (k = kh_begin(STATE->geoasn_countries);
            k != kh_end(STATE->geoasn_countries); ++k) {
      if (!kh_exist(STATE->geoasn_countries, k)) {
          continue;
      }
      pg = kh_val(STATE->geoasn_countries, k);
      per_geo_destroy(pg);
    }
    kh_destroy(geo_as, STATE->geoasn_countries);
  }

  if (STATE->geoasn_regions) {
    for (k = kh_begin(STATE->geoasn_regions);
          k != kh_end(STATE->geoasn_regions); ++k) {
      if (!kh_exist(STATE->geoasn_regions, k)) {
          continue;
      }
      pg = kh_val(STATE->geoasn_regions, k);
      per_geo_destroy(pg);
    }
    kh_destroy(geo_as, STATE->geoasn_regions);
  }

  if (STATE->ipmeta != NULL) {
    ipmeta_free(STATE->ipmeta);
    STATE->ipmeta = NULL;
  }

  if (STATE->records != NULL) {
    ipmeta_record_set_free(&STATE->records);
    STATE->records = NULL;
  }
}

static void destroy_pfx_user_ptr(void *user)
{
  perpfx_cache_t *pfx_cache = (perpfx_cache_t *)user;
  int i, j;
  khiter_t k;

  if (pfx_cache == NULL) {
    return;
  }

  for (i = 0; i < pfx_cache->continent_idxs_cnt; i++) {
    free(pfx_cache->continent_addr_runs[i]);
    pfx_cache->continent_addr_runs[i] = NULL;
    bgpstream_ipv6_pfx_set_destroy(pfx_cache->continent_addr6_pfxs[i]);
    pfx_cache->continent_addr6_pfxs[i] = NULL;
  }
  free(pfx_cache->continent_addr_runs);
  pfx_cache->continent_addr_runs = NULL;
  free(pfx_cache->continent_addr6_pfxs);
  pfx_cache->continent_addr6_pfxs = NULL;
  free(pfx_cache->continent_idxs);
  pfx_cache->continent_idxs = NULL;
  pfx_cache->continent_idxs_cnt = 0;
  free(pfx_cache->per_continent_addr_run_cnt);
  pfx_cache->per_continent_addr_run_cnt = NULL;

  for (i = 0; i < pfx_cache->country_idxs_cnt; i++) {
    free(pfx_cache->country_addr_runs[i]);
    pfx_cache->country_addr_runs[i] = NULL;
    bgpstream_ipv6_pfx_set_destroy(pfx_cache->country_addr6_pfxs[i]);
    pfx_cache->country_addr6_pfxs[i] = NULL;
  }
  free(pfx_cache->country_addr_runs);
  pfx_cache->country_addr_runs = NULL;
  free(pfx_cache->country_addr6_pfxs);
  pfx_cache->country_addr6_pfxs = NULL;
  free(pfx_cache->country_idxs);
  pfx_cache->country_idxs = NULL;
  pfx_cache->country_idxs_cnt = 0;
  free(pfx_cache->per_country_addr_run_cnt);
  pfx_cache->per_country_addr_run_cnt = NULL;

  for (j = 0; j < pfx_cache->poly_table_idxs_cnt; j++) {
    free(pfx_cache->poly_addr_runs[j]);
    pfx_cache->poly_addr_runs[j] = NULL;
    bgpstream_ipv6_pfx_set_destroy(pfx_cache->poly_addr6_pfxs[j]);
    pfx_cache->poly_addr6_pfxs[j] = NULL;
  }
  free(pfx_cache->poly_table_idxs);
  pfx_cache->poly_table_idxs = NULL;
  pfx_cache->poly_table_idxs_cnt = 0;
  free(pfx_cache->poly_addr_runs);
  free(pfx_cache->poly_addr6_pfxs);
  pfx_cache->poly_addr_runs = NULL;
  pfx_cache->poly_addr6_pfxs = NULL;
  free(pfx_cache->per_poly_addr_run_cnt);
  free(pfx_cache->per_poly_addr6_pfx_cnt);
  pfx_cache->per_poly_addr_run_cnt = NULL;
  pfx_cache->per_poly_addr6_pfx_cnt = NULL;

  for (k = kh_begin(pfx_cache->country_as_addr_runs);
          k != kh_end(pfx_cache->country_as_addr_runs); ++k) {
      ip_addr_run_set_t *runset;

      if (!kh_exist(pfx_cache->country_as_addr_runs, k)) {
          continue;
      }
      runset = kh_value(pfx_cache->country_as_addr_runs, k);
      free(runset->runs);
      free(runset);
  }
  kh_destroy(geo_as_run, pfx_cache->country_as_addr_runs);

  for (k = kh_begin(pfx_cache->region_as_addr_runs);
          k != kh_end(pfx_cache->region_as_addr_runs); ++k) {
      ip_addr_run_set_t *runset;

      if (!kh_exist(pfx_cache->region_as_addr_runs, k)) {
          continue;
      }
      runset = kh_value(pfx_cache->region_as_addr_runs, k);
      free(runset->runs);
      free(runset);
  }
  kh_destroy(geo_as_run, pfx_cache->region_as_addr_runs);

  free(pfx_cache);
}

static int clear_geocache(bvc_t *consumer, bgpview_t *view)
{
  bgpview_iter_t *it = bgpview_iter_create(view);
  assert(it != NULL);

  for (bgpview_iter_first_pfx(it, 0, BGPVIEW_FIELD_ALL_VALID); //
       bgpview_iter_has_more_pfx(it);                    //
       bgpview_iter_next_pfx(it)) {
    // will call the destroy func itself
    bgpview_iter_pfx_set_user(it, NULL);
  }

  bgpview_iter_destroy(it);
  return 0;
}

static int process_geoasn_line(bvc_t *consumer, char *buffer) {

  char *tok, *p;
  uint64_t asn;
  uint64_t key;
  int khret;
  khiter_t k;
  char keystr[1024];
  per_geo_t *pg;

  tok = strtok(buffer, ",");
  if (tok == NULL) {
      return -1;
  }

  errno = 0;
  asn = strtoul(tok, NULL, 10);
  if (errno) {
    fprintf(stderr, "Invalid ASN field: %s\n", tok);
    return -1;
  }

  while ((tok = strtok(NULL, ",")) != NULL) {
    if ((p = strchr(tok, '\n')) != NULL) {
      *p = '\0';
    }
    if (*tok == '\0') {
      break;
    }
    if (tok[0] >= '0' && tok[0] <= '9') {
      /* it is a region ID */
      errno = 0;
      key = strtoul(tok, NULL, 10);
      if (errno) {
          fprintf(stderr, "Invalid region ID: %s\n", tok);
          return -1;
      }
      key += (asn << 32);
      k = kh_put(geo_as, STATE->geoasn_regions, key, &khret);
      if (khret != 0) {
        snprintf(keystr, 1024, "%lu.%s", asn, tok);
        METRIC_PREFIX_INIT(pg, METRIC_PATH_GEOASN_REGION, keystr);
        kh_val(STATE->geoasn_regions, k) = pg;
      }
    } else {
      /* it is a country (hopefully) */
      if (strlen(tok) != 2) {
          fprintf(stderr, "Invalid country code: %s\n", tok);
          return -1;
      }
      key = (asn << 32) + (tok[0] << 8) + tok[1];
      k = kh_put(geo_as, STATE->geoasn_countries, key, &khret);
      if (khret != 0) {
        snprintf(keystr, 1024, "%lu.%s", asn, tok);
        METRIC_PREFIX_INIT(pg, METRIC_PATH_GEOASN_COUNTRY, keystr);
        kh_val(STATE->geoasn_countries, k) = pg;
      }
    }
  }
  return 0;
err:
  return -1;
}

static int load_geoasn_from_csv(bvc_t *consumer) {
  io_t *file;
  char buffer[2048];
  int read, rc = 1;

  if (STATE->geoasn_csv_file == NULL) {
      return 0;
  }

  if ((file = wandio_create(STATE->geoasn_csv_file)) == NULL) {
    fprintf(stderr, "ERROR: failed to open file '%s'\n",
        STATE->geoasn_csv_file);
    return -1;
  }

  while ((read = wandio_fgets(file, &buffer, 2048, 0)) > 0) {
    if (strlen(buffer) == 0) {
        continue;
    }
    if (process_geoasn_line(consumer, buffer) < 0) {
      fprintf(stderr, "Malformed line in region csv file: %s \n", buffer);
      rc = -1;
      break;
    }
  }
  wandio_destroy(file);
  return rc;
}

static int load_regions_from_csv(bvc_t *consumer) {
  io_t *file;
  char buffer[2048];
  int read;
  char *tok;
  int region_array_size = 5000;
  unsigned long reg_id;
  int i, rc = -1;

  if ((file = wandio_create(STATE->regions_csv_file)) == NULL) {
    fprintf(stderr, "ERROR: failed to open file '%s'\n",
        STATE->regions_csv_file);
    goto end;
  }

  STATE->polygons = calloc(region_array_size, sizeof(per_geo_t *));
  STATE->polygons_cnt = 0;

  while ((read = wandio_fgets(file, &buffer, 2048, 0)) > 0) {
    tok = strtok(buffer, ",");
    if (tok == NULL) {
      fprintf(stderr, "Malformed line in region csv file (should be id,fqid,name)\n");
      fprintf(stderr, "Line was: '%s'\n", buffer);
      goto end;
    }
    if (strcmp(tok, "ioda_region_id") == 0) {
        continue;
    }
    errno = 0;
    reg_id = strtoul(tok, NULL, 10);
    if (errno) {
        fprintf(stderr, "Invalid value for IODA region ID: %s", tok);
        continue;
    }

    tok = strtok(NULL, ",");
    if (tok == NULL) {
      fprintf(stderr, "Malformed line in region csv file (should be id,fqid,name)\n");
      goto end;
    }

    while (reg_id >= region_array_size) {
        region_array_size += 5000;
        STATE->polygons = realloc(STATE->polygons, region_array_size *
            sizeof(per_geo_t *));
        if (STATE->polygons == NULL) {
          fprintf(stderr, "Out of memory while expanding polygons array\n");
          goto end;
        }
        for (i = region_array_size - 5000; i < region_array_size; i++) {
          STATE->polygons[i] = NULL;
        }
    }

    assert(STATE->polygons[reg_id] == NULL);

    METRIC_PREFIX_INIT(STATE->polygons[reg_id], METRIC_PATH_NETACQ_EDGE_POLYS,
        tok);
    if (reg_id >= STATE->polygons_cnt) {
        STATE->polygons_cnt = reg_id + 1;
    }
  }
  rc = 0;
  fprintf(stderr, "Successfully created up to %u polygon array entries\n",
      STATE->polygons_cnt);

err:
end:
  wandio_destroy(file);
  return rc;
}

static int create_geo_pfxs_vis(bvc_t *consumer)
{
  int i, j;

  ipmeta_record_t **records;
  int records_cnt = 0;

  const char **countries_iso2 = NULL;
  const char **country_continents = NULL;
  const char **country_strings = NULL;

  int countries_cnt = 0;

  char cc_str[6] = "--.--";
  uint16_t country_idx;
  uint16_t continent_idx;

  char *cc_ptr;
  char *cc_cpy;
  int khret;
  khiter_t khiter;
  khash_t(strstr) *country_hash = kh_init(strstr);

  ipmeta_polygon_table_t **poly_tbls = NULL;
  ipmeta_polygon_table_t *table = NULL;

  /* ensure there are actually some records loaded */
  if ((records_cnt =
         ipmeta_provider_get_all_records(STATE->provider, &records)) == 0) {
    fprintf(stderr, "ERROR: Libipmeta is reporting no records loaded.\n");
    return -1;
  }
  free(records); /* @todo add a simple record count func to ipmeta */

  countries_cnt = ipmeta_provider_maxmind_get_iso2_list(&countries_iso2);
  if (ipmeta_provider_maxmind_get_country_continent_list(&country_continents)
      != countries_cnt) {
    fprintf(stderr, "ERROR: not all ISO2 country codes in libipmeta have a corresponding continent code?\n");
    return -1;
  }

  /* add state for each continent */
  for (i = 0; i < ARR_CNT(continent_strings); i++) {
    /* what is the index of this continent in the array? */
    continent_idx = CC_16(continent_strings[netacq_cont_map[i]]);

    METRIC_PREFIX_INIT(STATE->continents[continent_idx],
                       METRIC_PATH_NETACQ_EDGE_CONTINENT,
                       continent_strings[netacq_cont_map[i]]);
  }

  /* add state for each country */
  for (i = 0; i < countries_cnt; i++) {
    assert(countries_iso2[i] != NULL);
    assert(country_continents[i] != NULL);

    /* convert the ascii country code to a 16bit uint */
    country_idx = CC_16(countries_iso2[i]);

    /* build a string which contains the continent and country code*/
    cc_ptr = cc_str;
    cc_ptr = stpncpy(cc_ptr, country_continents[i],3);
    *cc_ptr = '.';
    cc_ptr++;
    stpncpy(cc_ptr, countries_iso2[i], 3);

    /* graphite dislikes metrics with *'s in them, replace with '-' */
    /* NOTE: this is only for the time series string */
    for (j = 0; j < strnlen(cc_str, 5); j++) {
      if (cc_str[j] == '*') {
        cc_str[j] = '-';
      }
    }

//    if ((cc_cpy = strndup(cc_str, 5)) == NULL) {
//      return -1;
//    }
//    khiter = kh_put(strstr, country_hash, countries[i]->iso3, &khret);
//    kh_value(country_hash, khiter) = cc_cpy;

    METRIC_PREFIX_INIT(STATE->countries[country_idx],
                       METRIC_PATH_NETACQ_EDGE_COUNTRY, cc_str);
  }

  kh_free_vals(strstr, country_hash, (void (*)(char *))free);
  kh_destroy(strstr, country_hash);

  /* add state for each region */
  if (load_regions_from_csv(consumer) < 0) {
      goto err;
  }

  STATE->geoasn_countries = kh_init(geo_as);
  STATE->geoasn_regions = kh_init(geo_as);
  if (load_geoasn_from_csv(consumer) < 0) {
      goto err;
  }

  return 0;

err:
  return -1;
}

static int lookup_polygon(bvc_pergeovisibility_state_t *state,
            bgpstream_pfx_t *pfx, perpfx_cache_t *pfx_cache,
            ipmeta_record_t *rec, uint64_t curr_address, uint64_t num_ips) {
  int i, khret;
  uint64_t as_key = 0, base_key = 0;
  khiter_t k;
  ip_addr_run_set_t *runset;

  base_key = rec->region_code;

  if (state->geoasn_regions) {
    /* Track the region-AS couplet */
    for (i = 0; i < state->valid_origins; i++) {
      as_key = base_key + (((uint64_t)state->origin_asns[i]) << 32);

      /* only track region-AS pairs that were explicitly requested */
      k = kh_get(geo_as, state->geoasn_regions, as_key);
      if (k == kh_end(state->geoasn_regions)) {
          continue;
      }
      k = kh_put(geo_as_run, pfx_cache->region_as_addr_runs, as_key, &khret);

      if (khret != 0) {
          /* new country-AS key */
        runset = calloc(1, sizeof(ip_addr_run_set_t));
        kh_val(pfx_cache->region_as_addr_runs, k) = runset;
      } else {
        runset = kh_val(pfx_cache->region_as_addr_runs, k);
      }

      runset->runs = update_ip_addr_run(runset->runs, &(runset->run_cnt),
            curr_address, num_ips);
    }
  }

  /* this is a polygon from one of the tables that we are tracking */
  /* check if it is already in our cache */
  for (i = 0; i < pfx_cache->poly_table_idxs_cnt; i++) {
    if (pfx_cache->poly_table_idxs[i] == rec->region_code) {
      return i;
    }
  }
  /* not in cache, add it */
  assert(pfx_cache->poly_table_idxs_cnt < UINT16_MAX);
  if ((pfx_cache->poly_table_idxs = realloc(pfx_cache->poly_table_idxs,
         sizeof(uint16_t) *
           (pfx_cache->poly_table_idxs_cnt + 1))) == NULL) {
    return -1;
  }

  ADD_ADDR_RUN(pfx_cache->poly_addr_runs,
               pfx_cache->per_poly_addr_run_cnt,
               pfx_cache->poly_table_idxs_cnt,
               sizeof(ip_addr_run_t), sizeof(uint64_t));

  ADD_V6_PFX_SET(pfx_cache->poly_addr6_pfxs,
               pfx_cache->poly_table_idxs_cnt);

  i = pfx_cache->poly_table_idxs_cnt;
  pfx_cache->poly_table_idxs_cnt ++;

  pfx_cache->poly_table_idxs[i] = rec->region_code;
  return i;
}

static int lookup_country(bvc_pergeovisibility_state_t *state,
            bgpstream_pfx_t *pfx, perpfx_cache_t *pfx_cache,
            ipmeta_record_t *rec, uint64_t curr_address, uint64_t num_ips) {

  int cont_idx = 0x3F3F;
  int i, khret;
  uint64_t as_key = 0, base_key = 0;
  khiter_t k;
  ip_addr_run_set_t *runset;

  if (rec->country_code[0] != '\0') {
    cont_idx = CC_16(rec->country_code);
  }

  if (state->geoasn_countries) {
    base_key = (rec->country_code[0] << 8) + (rec->country_code[1]);

    for (i = 0; i < state->valid_origins; i++) {
      as_key = base_key + (((uint64_t)state->origin_asns[i]) << 32);
      /* only track country-AS pairs that were explicitly requested */
      k = kh_get(geo_as, state->geoasn_countries, as_key);
      if (k == kh_end(state->geoasn_countries)) {
          continue;
      }
      k = kh_put(geo_as_run, pfx_cache->country_as_addr_runs, as_key, &khret);

      if (khret != 0) {
          /* new country-AS key */
          runset = calloc(1, sizeof(ip_addr_run_set_t));
          kh_val(pfx_cache->country_as_addr_runs, k) = runset;
      } else {
          runset = kh_val(pfx_cache->country_as_addr_runs, k);
      }

      runset->runs = update_ip_addr_run(runset->runs, &(runset->run_cnt),
              curr_address, num_ips);
    }
  }

  /* add country if it doesn't exist already */

  /** XXX performance? */
  for (i = 0; i < pfx_cache->country_idxs_cnt; i++) {
    if (pfx_cache->country_idxs[i] == cont_idx) {
      return i;
    }
  }

  /* no, add it. ooh. nasty realloc... */
  assert(pfx_cache->country_idxs_cnt < UINT8_MAX);
  if ((pfx_cache->country_idxs = realloc(
       pfx_cache->country_idxs,
       sizeof(uint16_t) * (pfx_cache->country_idxs_cnt + 1))) ==
       NULL) {
    return -1;
  }

  ADD_ADDR_RUN(pfx_cache->country_addr_runs,
               pfx_cache->per_country_addr_run_cnt,
               pfx_cache->country_idxs_cnt,
               sizeof(ip_addr_run_t), sizeof(uint64_t));
  ADD_V6_PFX_SET(pfx_cache->country_addr6_pfxs,
               pfx_cache->country_idxs_cnt);
  pfx_cache->country_idxs[pfx_cache->country_idxs_cnt++] = cont_idx;
  return pfx_cache->country_idxs_cnt - 1;
}

static int lookup_continent(perpfx_cache_t *pfx_cache, ipmeta_record_t *rec) {

  int cont_idx = 0x3F3F;
  int i, found;

  if (rec->continent_code[0] != '\0') {
    cont_idx = CC_16(rec->continent_code);
  }
  /* add continent if it doesn't exist already */
  found = 0;
  for (i = 0; i < pfx_cache->continent_idxs_cnt; i++) {
    if (pfx_cache->continent_idxs[i] == cont_idx) {
      found = 1;
      break;
    }
  }

  if (found) {
    return i;
  }

  /* no, add it. ooh. nasty realloc... */
  assert(pfx_cache->continent_idxs_cnt < UINT8_MAX);
  if ((pfx_cache->continent_idxs = realloc(
       pfx_cache->continent_idxs,
       sizeof(uint16_t) * (pfx_cache->continent_idxs_cnt + 1))) ==
       NULL) {
    return -1;
  }

  ADD_ADDR_RUN(pfx_cache->continent_addr_runs,
               pfx_cache->per_continent_addr_run_cnt,
               pfx_cache->continent_idxs_cnt,
               sizeof(ip_addr_run_t), sizeof(uint64_t));
  ADD_V6_PFX_SET(pfx_cache->continent_addr6_pfxs,
               pfx_cache->continent_idxs_cnt);

  pfx_cache->continent_idxs[pfx_cache->continent_idxs_cnt++] = cont_idx;
  return pfx_cache->continent_idxs_cnt - 1;
}

static int update_pfx_v6(bvc_t *consumer, bgpstream_pfx_t *pfx,
                perpfx_cache_t *pfx_cache, uint64_t *iptally) {
  uint64_t num_ips = 0;
  uint64_t cur_address = first_pfx_addr(pfx);
  ipmeta_record_t *rec = NULL;

  /* Perform lookup */
  ipmeta_record_set_clear(STATE->records);
  ipmeta_lookup_pfx(STATE->ipmeta, AF_INET6,
                  (void *)(&(pfx->address.bs_ipv6.addr.s6_addr)),
                  pfx->mask_len, 0, STATE->records);

  ipmeta_record_set_rewind(STATE->records);

  while ((rec = ipmeta_record_set_next(STATE->records, &num_ips))) {
    int ind;

    ind = lookup_continent(pfx_cache, rec);
    if (ind < 0) {
      return -1;
    }
    if ((pfx_cache->continent_addr6_pfxs[ind] =
        update_ip6_prefix(pfx_cache->continent_addr6_pfxs[ind],
                           cur_address, num_ips)) == NULL) {
      return -1;
    }

    ind = lookup_country(STATE, pfx, pfx_cache, rec, cur_address, num_ips);
    if (ind < 0) {
      return -1;
    }
    if ((pfx_cache->country_addr6_pfxs[ind] =
        update_ip6_prefix(pfx_cache->country_addr6_pfxs[ind],
                           cur_address, num_ips)) == NULL) {
      return -1;
    }

    ind = lookup_polygon(STATE, pfx, pfx_cache, rec, cur_address, num_ips);
    if (ind < 0) {
      return -1;
    }
    if ((pfx_cache->poly_addr6_pfxs[ind] =
        update_ip6_prefix(pfx_cache->poly_addr6_pfxs[ind],
                cur_address, num_ips)) == NULL) {
      return -1;
    }

    cur_address += num_ips;
    (*iptally) += num_ips;
  }
  return 0;
}

static int update_pfx_v4(bvc_t *consumer, bgpstream_pfx_t *pfx,
        perpfx_cache_t *pfx_cache, uint64_t *iptally) {
  uint64_t num_ips = 0;
  uint64_t cur_address = first_pfx_addr(pfx);
  ipmeta_record_t *rec = NULL;

  /* Perform lookup */
  ipmeta_record_set_clear(STATE->records);
  ipmeta_lookup_pfx(STATE->ipmeta, AF_INET,
                  (void *)(&(pfx->address.bs_ipv4.addr.s_addr)),
                  pfx->mask_len, 0, STATE->records);

  ipmeta_record_set_rewind(STATE->records);

  while ((rec = ipmeta_record_set_next(STATE->records, &num_ips))) {
    int ind;

    ind = lookup_continent(pfx_cache, rec);
    if (ind < 0) {
      return -1;
    }
    if ((pfx_cache->continent_addr_runs[ind] =
        update_ip_addr_run(pfx_cache->continent_addr_runs[ind],
                           &(pfx_cache->per_continent_addr_run_cnt[ind]),
                           cur_address, num_ips)) == NULL) {
      return -1;
    }

    ind = lookup_country(STATE, pfx, pfx_cache, rec, cur_address, num_ips);
    if (ind < 0) {
      return -1;
    }
    if ((pfx_cache->country_addr_runs[ind] =
        update_ip_addr_run(pfx_cache->country_addr_runs[ind],
                           &(pfx_cache->per_country_addr_run_cnt[ind]),
                           cur_address, num_ips)) == NULL) {
      return -1;
    }

    ind = lookup_polygon(STATE, pfx, pfx_cache, rec, cur_address, num_ips);
    if (ind < 0) {
      return -1;
    }
    if ((pfx_cache->poly_addr_runs[ind] =
        update_ip_addr_run(pfx_cache->poly_addr_runs[ind],
             &(pfx_cache->per_poly_addr_run_cnt[ind]),
             cur_address, num_ips)) == NULL) {
      return -1;
    }

    (*iptally) += num_ips;
    cur_address += num_ips;
  }
  return 0;
}

static int update_pfx_geo_information(bvc_t *consumer, bgpview_iter_t *it)
{
  bgpstream_pfx_t *pfx = bgpview_iter_pfx_get_pfx(it);
  perpfx_cache_t *pfx_cache = (perpfx_cache_t *)bgpview_iter_pfx_get_user(it);

  uint64_t num_ips = 0;
  uint64_t cur_address = first_pfx_addr(pfx);
  ipmeta_record_t *rec = NULL;

  int i;
  uint16_t cont_idx = 0x3F3F;
  uint16_t country_idx = 0x3F3F;
  int found;
  int rec_c = 0;

  per_geo_t *pg;
  khiter_t k, k_pg;
  ip_addr_run_set_t *runs;

  /* if the user pointer (cache) does not exist, then do the lookup now */
  if (pfx_cache == NULL) {
    if ((pfx_cache = malloc_zero(sizeof(perpfx_cache_t))) == NULL) {
      fprintf(stderr, "Error: cannot create per-pfx cache\n");
      return -1;
    }

    pfx_cache->country_as_addr_runs = kh_init(geo_as_run);
    pfx_cache->region_as_addr_runs = kh_init(geo_as_run);

    if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
      if (update_pfx_v4(consumer, pfx, pfx_cache, &num_ips) < 0) {
        return -1;
      }
    } else if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV6) {
      if (update_pfx_v6(consumer, pfx, pfx_cache, &num_ips) < 0) {
        return -1;
      }
    } else {
      /* Skip any non-v4 and non-v6 prefixes */
      return 0;
    }

    /* link the cache to the appropriate user ptr */
    bgpview_iter_pfx_set_user(it, pfx_cache);
  }

  /* Ensure that the sum of IPInfo block lengths is identical to the number
   * of addresses in the given prefix.  This is a crucial assumption for our
   * algorithm.
   */
  if (first_pfx_addr(pfx) + num_ips != (last_pfx_addr(pfx) + 1) && \
      num_ips != 0) {
    char buf[256];
    fprintf(stderr, "ERROR: Sum of IPInfo blocks (%lu) and number of "
                    "addresses in prefix (%lu) are not identical.  Does "
                    "IPInfo have gaps?\n",
                    num_ips, last_pfx_addr(pfx) - first_pfx_addr(pfx) + 1);
    fprintf(stderr, "Ignoring the prefix: %s\n", bgpstream_pfx_snprintf(buf, 256, pfx));
    return 0;
  }

  /* now the prefix cache holds geo info we can update the counters for each
   * aggregate (continents, countries, polygons) */

  /* continents */
  for (i = 0; i < pfx_cache->continent_idxs_cnt; i++) {

    if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
      if (per_geo_update(consumer,
                       STATE->continents[pfx_cache->continent_idxs[i]],
                       pfx,
                       pfx_cache->continent_addr_runs[i],
                       pfx_cache->per_continent_addr_run_cnt[i], 0) != 0) {
        return -1;
      }
    } else if (per_geo_update_v6(consumer,
                       STATE->continents[pfx_cache->continent_idxs[i]],
                       pfx,
                       pfx_cache->continent_addr6_pfxs[i]) != 0) {
      return -1;
    }
  }

  /* countries */
  for (i = 0; i < pfx_cache->country_idxs_cnt; i++) {
    if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
      if (per_geo_update(consumer, STATE->countries[pfx_cache->country_idxs[i]],
                       pfx,
                       pfx_cache->country_addr_runs[i],
                       pfx_cache->per_country_addr_run_cnt[i],
                       pfx_cache->country_idxs[i]) != 0) {
        return -1;
      }
    } else if (per_geo_update_v6(consumer,
                       STATE->countries[pfx_cache->country_idxs[i]],
                       pfx,
                       pfx_cache->country_addr6_pfxs[i]) != 0) {
      return -1;
    }
  }

  /* polygons (possibly many per table) */
  for (i = 0; i < pfx_cache->poly_table_idxs_cnt; i++) {
    if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
      if (per_geo_update(
            consumer,
            STATE->polygons[pfx_cache->poly_table_idxs[i]],
            pfx,
            pfx_cache->poly_addr_runs[i],
            pfx_cache->per_poly_addr_run_cnt[i], 0) != 0) {
        return -1;
      }
    } else if (per_geo_update_v6(consumer,
          STATE->polygons[pfx_cache->poly_table_idxs[i]],
          pfx,
          pfx_cache->poly_addr6_pfxs[i]) != 0) {
      return -1;
    }
  }

  if (STATE->geoasn_countries) {
    for (k = kh_begin(pfx_cache->country_as_addr_runs);
          k != kh_end(pfx_cache->country_as_addr_runs); ++k) {
      if (!kh_exist(pfx_cache->country_as_addr_runs, k)) {
        continue;
      }
      k_pg = kh_get(geo_as, STATE->geoasn_countries,
          kh_key(pfx_cache->country_as_addr_runs, k));
      if (k_pg == kh_end(STATE->geoasn_countries)) {
        continue;
      }

      runs = kh_val(pfx_cache->country_as_addr_runs, k);
      pg = kh_val(STATE->geoasn_countries, k_pg);

      if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
        if (per_geo_update(consumer, pg, pfx, runs->runs,
                    runs->run_cnt, 0) != 0) {
          return -1;
        }
      } else {
        /* TODO IPv6 ... */
      }
    }
  }

  if (STATE->geoasn_regions) {
    for (k = kh_begin(pfx_cache->region_as_addr_runs);
          k != kh_end(pfx_cache->region_as_addr_runs); ++k) {
      if (!kh_exist(pfx_cache->region_as_addr_runs, k)) {
        continue;
      }
      k_pg = kh_get(geo_as, STATE->geoasn_regions,
          kh_key(pfx_cache->region_as_addr_runs, k));
      if (k_pg == kh_end(STATE->geoasn_regions)) {
        continue;
      }

      runs = kh_val(pfx_cache->region_as_addr_runs, k);
      pg = kh_val(STATE->geoasn_regions, k_pg);

      if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
        if (per_geo_update(consumer, pg, pfx, runs->runs,
                    runs->run_cnt, 0) != 0) {
          return -1;
        }
      } else {
        /* TODO IPv6 ... */
      }
    }
  }

  return 0;
}

static int compute_geo_pfx_visibility(bvc_t *consumer, bgpview_iter_t *it)
{
  bgpstream_pfx_t *pfx;
  bgpstream_peer_sig_t *sg;

  /* for each prefix in the view */
  for (bgpview_iter_first_pfx(it, 0, BGPVIEW_FIELD_ACTIVE); //
       bgpview_iter_has_more_pfx(it);                //
       bgpview_iter_next_pfx(it)) {

    pfx = bgpview_iter_pfx_get_pfx(it);

    /* only consider (ipv4) prefixes mask is longer than a /6 */
    if (pfx->mask_len <
        BVC_GET_CHAIN_STATE(consumer)->pfx_vis_mask_len_threshold) {
      continue;
    }

    /* reset information for the current prefix */
    bgpstream_id_set_clear(STATE->ff_asns);
    STATE->valid_origins = 0;

    /* iterate over the peers for the current pfx and get the number of unique
     * full feed AS numbers observing this prefix as well as the unique set of
     * origin ASes */
    for (bgpview_iter_pfx_first_peer(it, BGPVIEW_FIELD_ACTIVE); //
         bgpview_iter_pfx_has_more_peer(it);                    //
         bgpview_iter_pfx_next_peer(it)) {

      /* only consider peers that are full-feed (checking if peer id is a full
       * feed for the current pfx IP version) */
      if (bgpstream_id_set_exists(
            BVC_GET_CHAIN_STATE(consumer)
              ->full_feed_peer_ids[bgpstream_ipv2idx(pfx->address.version)],
            bgpview_iter_peer_get_peer_id(it)) == 0) {
        continue;
      }

      /* get peer signature */
      sg = bgpview_iter_peer_get_sig(it);
      assert(sg != NULL);

      /* Add peer AS number to set of full feed peers observing the prefix */
      bgpstream_id_set_insert(STATE->ff_asns, sg->peer_asnumber);

      /* Add origin AS number to the array of origin ASNs for the prefix */
      add_origin(STATE, bgpview_iter_pfx_peer_get_origin_seg(it));
    }

    if (STATE->valid_origins > 0 &&
        update_pfx_geo_information(consumer, it) != 0) {
      return -1;
    }
  }

  return 0;
}

static int update_per_geo_metrics(bvc_t *consumer, per_geo_t *pg, int index)
{
  int i;
  for (i = VIS_THRESHOLDS_CNT - 1; i >= 0; i--) {
    /* we merge all the trees (asn sets) with the previous one, except the
     * first */
    if (i != (VIS_THRESHOLDS_CNT - 1)) {
      bgpstream_patricia_tree_merge(pg->thresholds[i].pfxs,
                                    pg->thresholds[i + 1].pfxs);
      bgpstream_id_set_merge(pg->thresholds[i].asns,
                             pg->thresholds[i + 1].asns);
      bgpstream_id_set_merge(pg->thresholds[i].asns_v6,
                             pg->thresholds[i + 1].asns_v6);
      slash24_id_set_merge(pg->thresholds[i].slash24s,
                           pg->thresholds[i + 1].slash24s);
      bgpstream_patricia_tree_merge(pg->thresholds[i].v6_subnets,
                                    pg->thresholds[i+1].v6_subnets);
    }

    /* now that the tree represents all the prefixes that match the threshold,
     * we extract the information that we want to output */

    /* IPv4*/
    timeseries_kp_set(
      STATE->kp, pg->thresholds[i]
                   .pfx_cnt_idx[bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4)],
      bgpstream_patricia_prefix_count(pg->thresholds[i].pfxs,
                                      BGPSTREAM_ADDR_VERSION_IPV4));



    timeseries_kp_set(
      STATE->kp,
      pg->thresholds[i]
        .subnet_cnt_idx[bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4)],
      //bgpstream_patricia_tree_count_24subnets(pg->thresholds[i].pfxs));
      slash24_id_set_size(pg->thresholds[i].slash24s));

    timeseries_kp_set(
      STATE->kp,
      pg->thresholds[i]
        .asns_cnt_idx[bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4)],
      bgpstream_id_set_size(pg->thresholds[i].asns));

    /* IPv6 */
    timeseries_kp_set(
      STATE->kp, pg->thresholds[i]
                   .pfx_cnt_idx[bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV6)],
      bgpstream_patricia_prefix_count(pg->thresholds[i].pfxs,
                                      BGPSTREAM_ADDR_VERSION_IPV6));

    timeseries_kp_set(
      STATE->kp,
      pg->thresholds[i]
        .subnet_cnt_idx[bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV6)],
      bgpstream_patricia_tree_count_64subnets(pg->thresholds[i].v6_subnets));

    timeseries_kp_set(
      STATE->kp,
      pg->thresholds[i]
        .asns_cnt_idx[bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV6)],
      bgpstream_id_set_size(pg->thresholds[i].asns_v6));
  }

  /* metrics are set, now we have to clean the patricia trees and sets */
  for (i = VIS_THRESHOLDS_CNT - 1; i >= 0; i--) {
    bgpstream_patricia_tree_clear(pg->thresholds[i].pfxs);
    bgpstream_id_set_clear(pg->thresholds[i].asns);
    bgpstream_id_set_clear(pg->thresholds[i].asns_v6);
    slash24_id_set_clear(pg->thresholds[i].slash24s);
    bgpstream_patricia_tree_clear(pg->thresholds[i].v6_subnets);
  }

  return 0;
}

static int update_metrics(bvc_t *consumer)
{
  int i;
  khiter_t k;
  per_geo_t *pg;

  /* for each continent and country */
  for (i = 0; i < METRIC_ISO2_ASCII_MAX; i++) {
    if (STATE->continents[i] != NULL &&
        update_per_geo_metrics(consumer, STATE->continents[i], 0) != 0) {
      return -1;
    }

    if (STATE->countries[i] != NULL &&
        update_per_geo_metrics(consumer, STATE->countries[i], i) != 0) {
      return -1;
    }
  }

  /* for each polygon */
  for (i = 0; i < STATE->polygons_cnt; i++) {
    if (STATE->polygons[i] != NULL &&
        update_per_geo_metrics(consumer, STATE->polygons[i], 0) != 0) {
      return -1;
    }
  }

  /* for each asn-country couplet */
  if (STATE->geoasn_countries) {
    for (k = kh_begin(STATE->geoasn_countries);
        k != kh_end(STATE->geoasn_countries); ++k) {
      if (!kh_exist( STATE->geoasn_countries, k)) {
        continue;
      }
      pg = kh_value(STATE->geoasn_countries, k);
      if (update_per_geo_metrics(consumer, pg, 0) != 0) {
        return -1;
      }
    }
  }

  /* for each asn-country couplet */
  if (STATE->geoasn_regions) {
    for (k = kh_begin(STATE->geoasn_regions);
        k != kh_end(STATE->geoasn_regions); ++k) {
      if (!kh_exist( STATE->geoasn_regions, k)) {
        continue;
      }
      pg = kh_value(STATE->geoasn_regions, k);
      if (update_per_geo_metrics(consumer, pg, 0) != 0) {
        return -1;
      }
    }
  }
  return 0;
}

/* ==================== CONSUMER INTERFACE FUNCTIONS ==================== */

bvc_t *bvc_pergeovisibility_ipinfo_alloc()
{
  return &bvc_pergeovisibility_ipinfo;
}

int bvc_pergeovisibility_ipinfo_init(bvc_t *consumer, int argc, char **argv)
{
  bvc_pergeovisibility_state_t *state = NULL;

  if ((state = malloc_zero(sizeof(bvc_pergeovisibility_state_t))) == NULL) {
    return -1;
  }
  BVC_SET_STATE(consumer, state);

  /* set defaults here */

  /* init and set defaults */

  if ((state->ff_asns = bgpstream_id_set_create()) == NULL) {
    fprintf(stderr, "Error: Could not create full feed origin ASNs set\n");
    goto err;
  }

  if (init_kp(consumer) != 0) {
    fprintf(stderr, "ERROR: Could not initialize timeseries KP\n");
    goto err;
  }

  /* parse the command line args */
  if (parse_args(consumer, argc, argv) != 0) {
    goto err;
  }

  /* initialize ipmeta and provider */
  if (init_ipmeta(consumer) != 0) {
    usage(consumer);
    return -1;
  }

  /* the main hash table can be created only when ipmeta has been
   * properly initialized */
  if (create_geo_pfxs_vis(consumer) != 0) {
    usage(consumer);
    goto err;
  }

  /* get full feed peer ids from Visibility */
  if (BVC_GET_CHAIN_STATE(consumer)->visibility_computed == 0) {
    fprintf(stderr,
            "ERROR: The Per-Geo Visibility requires the Visibility consumer "
            "to be run first\n");
    goto err;
  }

  return 0;

err:
  bvc_pergeovisibility_ipinfo_destroy(consumer);
  return -1;
}

void bvc_pergeovisibility_ipinfo_destroy(bvc_t *consumer)
{
  if (STATE == NULL) {
    return;
  }

  destroy_ipmeta(consumer);

  free(STATE->provider_config);
  free(STATE->regions_csv_file);
  if (STATE->geoasn_csv_file) {
    free(STATE->geoasn_csv_file);
  }
  STATE->provider_config = NULL;
  STATE->provider_name = NULL;
  STATE->provider_arg = NULL;
  STATE->regions_csv_file = NULL;
  STATE->geoasn_csv_file = NULL;

  if (STATE->ff_asns != NULL) {
    bgpstream_id_set_destroy(STATE->ff_asns);
    STATE->ff_asns = NULL;
  }

  timeseries_kp_free(&STATE->kp);

  free(STATE);

  BVC_SET_STATE(consumer, NULL);
}

int bvc_pergeovisibility_ipinfo_process_view(bvc_t *consumer, bgpview_t *view)
{
  /* META metric values */
  uint32_t arrival_delay;
  uint32_t processed_delay;
  uint32_t processing_time;

  /* set the pfx user pointer destructor function */
  bgpview_set_pfx_user_destructor(view, destroy_pfx_user_ptr);

  if (STATE->last_reload == 0) {
    STATE->last_reload = bgpview_get_time(view);
  }

  /* should we reload the ipmeta instance? (to pick up a new database) */
  if (STATE->reload_freq > 0 &&
      bgpview_get_time(view) >= (STATE->last_reload + STATE->reload_freq)) {
    fprintf(stderr, "INFO: reloading libipmeta (after %"PRIu32" seconds)\n",
            (bgpview_get_time(view) - STATE->last_reload));
    /* clear our cache */
    clear_geocache(consumer, view);

    /* shut down our existing ipmeta instance */
    destroy_ipmeta(consumer);

    /* create a new key package */
    timeseries_kp_free(&STATE->kp);
    if (init_kp(consumer) != 0) {
      fprintf(stderr, "ERROR: Could not re-initialize the timeseries KP\n");
      return -1;
    }

    /* restart ipmeta */
    if (init_ipmeta(consumer) != 0) {
      fprintf(stderr, "ERROR: Could not restart ipmeta\n");
      return -1;
    }

    /* recreate other ipmeta state */
    if (create_geo_pfxs_vis(consumer) != 0) {
      fprintf(stderr, "ERROR: Could not rebuild ipmeta lookup tables\n");
      return -1;
    }

    STATE->last_reload = bgpview_get_time(view);
  }

  if (BVC_GET_CHAIN_STATE(consumer)
        ->usable_table_flag[bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4)] ==
      0) {
    fprintf(stderr,
            "WARN: View (%" PRIu32 ") is unusable for Per-Geo Visibility\n",
            bgpview_get_time(view));
    return 0;
  }

  /* compute arrival delay */
  arrival_delay = epoch_sec() - bgpview_get_time(view);

  /* create a new iterator */
  bgpview_iter_t *it;
  if ((it = bgpview_iter_create(view)) == NULL) {
    return -1;
  }

  /* compute the pfx visibility stats for each geo aggregation (continent,
     country, region, county) */
  if (compute_geo_pfx_visibility(consumer, it) != 0) {
    return -1;
  }

  /* destroy the view iterator */
  bgpview_iter_destroy(it);

  /* compute the metrics and reset the state variables */
  if (update_metrics(consumer) != 0) {
    return -1;
  }

  /* compute delays */
  processed_delay = epoch_sec() - bgpview_get_time(view);
  processing_time = processed_delay - arrival_delay;

  /* set delays metrics */
  timeseries_kp_set(STATE->kp, STATE->arrival_delay_idx, arrival_delay);
  timeseries_kp_set(STATE->kp, STATE->processed_delay_idx, processed_delay);
  timeseries_kp_set(STATE->kp, STATE->processing_time_idx, processing_time);

  /* now flush the KP */
  if (timeseries_kp_flush(STATE->kp, bgpview_get_time(view)) != 0) {
    fprintf(stderr, "Warning: could not flush %s %" PRIu32 "\n", NAME,
            bgpview_get_time(view));
  }

  return 0;
}
