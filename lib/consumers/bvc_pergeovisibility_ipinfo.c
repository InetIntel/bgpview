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


#include "bgpview_consumer_interface.h"
#include "bvc_pergeovisibility_ipinfo.h"
#include "bgpstream_utils_pfx_set.h"
#include "bgpstream_utils_patricia.h"

#include "khash.h"
#include "utils.h"
#include "libipmeta.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>

#define NAME "per-geo-visibility-ipinfo"
#define METRIC_PREFIX "prefix-visibility"

#define METRIC_PATH "geo.ipinfo"

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
  "SA", // South America
};

/** Convert a 2 char byte array to a 16 bit number */
#define CC_16(bytes) ((bytes[0] << 8) | bytes[1])

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

KHASH_MAP_INIT_STR(name_map, per_geo_t)
KHASH_MAP_INIT_INT(iso2_map, per_geo_t)

KHASH_MAP_INIT_INT(iso2_runs, pfx_location_t);
KHASH_MAP_INIT_STR(name_runs, pfx_location_t);

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

#define STATE (BVC_GET_STATE(consumer, pergeovisibility))

#define CHAIN_STATE (BVC_GET_CHAIN_STATE(consumer))

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


static bvc_t bvc_pergeovisibility_ipinfo = {
  BVC_ID_PERGEOVISIBILITY_IPINFO,            // ID
  NAME,                                      // Name
  BVC_GENERATE_PTRS(pergeovisibility_ipinfo) // Generate function pointers
};

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

typedef struct pfx_location {
    ip_addr_run_t *addr_runs;
    bgpstream_ipv6_pfx_set_t *addr6_pfxs;

    uint64_t addr_run_cnt;
    uint64_t addr_run_size;
} pfx_location_t;

typedef struct perpfx_cache {
    khash_t(iso2_runs) continents;
    khash_t(iso2_runs) countries;
    khash_t(name_runs) regions;
    khash_t(name_runs) cities;

} perpfx_cache_t;

/* our 'instance' */
typedef struct bvc_pergeovisibility_state {

    /** ipmeta structures */
    char *provider_config;
    char *provider_name;
    char *provider_arg;

    ipmeta_t *ipmeta;
    ipmeta_provider_t *provider;
    ipmeta_record_set_t *records;

    khash_t(iso2_map) *continents;
    khash_t(iso2_map) *countries;
    khash_t(name_map) *regions;
    khash_t(name_map) *cities;

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

} bvc_pergeovisibility_ipinfo_state_t;

/* ==================== PARSE ARGS FUNCTIONS ==================== */

/** Print usage information to stderr */
static void usage(bvc_t *consumer)
{
    fprintf(stderr, "consumer usage: %s -p <ipmeta-provider>\n",
            consumer->name);
}

static int parse_args(bvc_t *consumer, int argc, char **argv) {
    int opt;
    assert(argc > 0 && argv != NULL);

    optind = 1;
    while ((opt = getopt(argc, argv, ":p:r:?")) >= 0) {
        switch(opt) {
            case 'p':
                STATE->provider_config = strdup(optarg);
                break;
            case 'r':
                STATE->reload_freq = atoi(optarg);
                break;
            case '?':
            case ':':
            default:
                usage(consumer);
                return -1;
        }
    }

    if (STATE->provider_config == NULL) {
        fprintf(stderr,
                "ERROR: geolocation provider must be configured using -p\n");
        usage(consumer);
        return -1;
    }
    return 0;
}

/* ==================== ORIGINS FUNCTIONS ==================== */

/* check if an origin ASN is already part of the array and
 * if not it adds it */
static void add_origin(bvc_pergeovisibility_ipinfo_state_t *state,
                       bgpstream_as_path_seg_t *origin_seg) {
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
                pfx_location_t *loc,
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

    if (loc->addr6_pfxs == NULL) {
        loc->addr6_pfxs = bgpstream_ipv6_pfx_set_create();
    }

    /* Use bgpstream_ipv6_pfx_set_insert() to add to the prefix set */
    bgpstream_ipv6_pfx_set_insert(loc->addr6_pfxs, &(newpfx.bs_ipv6));

    return loc->addr6_pfxs;
}

static ip_addr_run_t *update_ip_addr_run(pfx_location_t *loc,
                                         uint64_t cur_address,
                                         uint64_t num_ips) {
    ip_addr_run_t *run = NULL;

    /* If the given addr_runs has not been allocated yet, we are dealing with a
     * new location.  In this case, we allocate storage, populate it with our
     * genesis address, and return a pointer to the newly-allocated storage.
     */
    if (loc->addr_runs == NULL) {
        if ((loc->addr_runs = calloc(10, sizeof(ip_addr_run_t))) == NULL) {
            fprintf(stderr, "OOM inside update_ip_addr_run() \n");
            return NULL;
        }
        loc->addr_run_cnt = 1;
        loc->addr_run_size = 10;

        run = &(loc->addr_runs[0]);
        run->network_addr = cur_address;
        run->num_ips = num_ips;

        return loc->addr_runs;
    }

    assert(loc->addr_run_cnt > 0);
    run = &(addr_runs[loc->addr_run_cnt - 1]);
    assert(run->network_addr != cur_address);

    /* We are dealing with a continuation of a past run.  All we need to do is
     * add the number of new IP addresses to the past run.
     */
    if (cur_address == (run->network_addr + run->num_ips)) {
        run->num_ips += num_ips;
        /* We are dealing with a new run for a country that already has runs.
         * We have to add a new ip_addr_run_t data structure and populate it.
         */
    } else {
        if (loc->addr_run_cnt == loc->addr_run_size) {
            loc->addr_runs = realloc(loc->addr_runs,
                    sizeof(ip_addr_run_t) * (loc->addr_run_size + 10));
            if (loc->addr_runs == NULL) {
                fprintf(stderr, "OOM inside update_ip_addr_run() \n");
                return NULL;
            }
        }
        loc->addr_run_cnt ++;

        run = &(addr_runs[loc->addr_run_cnt - 1]);
        run->network_addr = cur_address;
        run->num_ips = num_ips;
    }

    return loc->addr_runs;
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
        METRIC_KEY_INIT(pt->subnet_cnt_idx[v], metric_pfx,
                bgpstream_idx2number(v),
                thresh_str,
                v == bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4)
                ? "visible_slash24_cnt"
                : "visible_slash64_cnt");

        /* visible_asns_cnt */
        METRIC_KEY_INIT(pt->asns_cnt_idx[v], metric_pfx,
                bgpstream_idx2number(v), thresh_str, "visible_asns_cnt");
    }

    return 0;

err:
    return -1;
}

static per_geo_t *per_geo_init(bvc_t *consumer, const char *metric_pfx) {
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

static void add_geo_v6pfx_to_tree(bgpstream_pfx_t *pfx, void *userdata) {
    per_thresh_t *pt = (per_thresh_t *)userdata;
    bgpstream_patricia_tree_insert(pt->v6_subnets, pfx);
}

static int per_geo_update_v6(bvc_t *consumer, per_geo_t *pg,
                bgpstream_pfx_t *pfx, pfx_location_t *loc) {

    uint32_t num_slash24s, offset = 0;
    int idx = bgpstream_ipv2idx(pfx->address.version);
    /* number of full feed ASNs for the current IP version*/
    int totalfullfeed = CHAIN_STATE->full_feed_peer_asns_cnt[idx];
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
            if (bgpstream_patricia_tree_insert(pg->thresholds[i].pfxs,
                    pfx) == NULL) {
                return -1;
            }
            /* add origin ASNs to asns set */
            for (j = 0; j < STATE->valid_origins; j++) {

                bgpstream_id_set_insert(pg->thresholds[i].asns_v6,
                        STATE->origin_asns[j]);
            }

            if (bgpstream_ipv6_pfx_set_iterate(loc->addr6_pfxs,
                        add_geo_v6pfx_to_tree,
                        (void *) &(pg->thresholds[i])) < 0) {
                return -1;
            }
            break;
        }
    }
    return 0;
}

static int per_geo_update(bvc_t *consumer, per_geo_t *pg, bgpstream_pfx_t *pfx,
        pfx_location_t *loc) {

    uint32_t num_slash24s, offset = 0;
    int idx = bgpstream_ipv2idx(pfx->address.version);
    /* number of full feed ASNs for the current IP version*/
    int totalfullfeed = CHAIN_STATE->full_feed_peer_asns_cnt[idx];
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
            if (bgpstream_patricia_tree_insert(pg->thresholds[i].pfxs,
                    pfx) == NULL) {
                return -1;
            }
            /* add origin ASNs to asns set */
            for (j = 0; j < STATE->valid_origins; j++) {

                bgpstream_id_set_insert(pg->thresholds[i].asns,
                        STATE->origin_asns[j]);
            }
            /* "Explode" each run into a series of /24 or /64 networks and
             * add them to the set.
             */
            for (j = 0; j < loc->addr_run_cnt; j++) {
                /* Determine the offset to the beginning of the /24. */
                offset = loc->addr_runs[j].network_addr & 0x000000ff;
                /* Round up to the next-highest number of /24 */
                num_slash24s = (loc->addr_runs[j].num_ips + offset + 255) / 256;

                for (k = 0; k < num_slash24s; k++) {
                    slash24_id_set_insert(pg->thresholds[i].slash24s,
                            (loc->addr_runs[j].network_addr & 0xffffff00) +
                                    (k << 8));
                }
            }
            break;
        }
    }
    return 0;
}

static void per_geo_destroy(per_geo_t *pg) {
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
    if ((STATE->arrival_delay_idx = timeseries_kp_add_key(STATE->kp,
            buffer)) == -1) {
        return -1;
    }
    snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
            CHAIN_STATE->metric_prefix, "processed_delay");
    if ((STATE->processed_delay_idx = timeseries_kp_add_key(STATE->kp,
            buffer)) == -1) {
        return -1;
    }
    snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
            CHAIN_STATE->metric_prefix, "processing_time");
    if ((STATE->processing_time_idx = timeseries_kp_add_key(STATE->kp,
            buffer)) == -1) {
        return -1;
    }

    return 0;
}

static int init_ipmeta(bvc_t *consumer) {
    /* initialize ipmeta structure */
    if ((STATE->ipmeta = ipmeta_init(IPMETA_DS_PATRICIA)) == NULL) {
        fprintf(stderr, "Error: Could not initialize ipmeta \n");
        return -1;
    }

    if (STATE->provider_name == NULL) {
        /* need to parse the string given by the user */
        assert(STATE->provider_arg == NULL);
        STATE->provider_name = STATE->provider_config;

        /* the string at STATE->provider_config will contain the name of the
         * plugin, optionally followed by a space and then the arguments to
         * pass to the plugin */
        if ((STATE->provider_arg = strchr(STATE->provider_config, ' '))
                != NULL) {
            /* set the space to a nul, which allows STATE->provider_configs[i]
             * to be used for the provider name, and then increment
             * plugin_arg_ptr to point to the next character, which will be
             * the start of the arg string (or at worst case, the
             * terminating \0) */
            *STATE->provider_arg = '\0';
            STATE->provider_arg++;
        }
    }
    /* lookup the provider using the name given  */
    if ((STATE->provider = ipmeta_get_provider_by_name(
                    STATE->ipmeta, STATE->provider_name)) == NULL) {
        fprintf(stderr, "ERROR: Invalid provider name: %s\n",
                STATE->provider_name);
        return -1;
    }

    /* we only support ipinfo or the memcache-psql provider */
    if (ipmeta_get_provider_id(STATE->provider) != IPMETA_PROVIDER_IPINFO &&
            ipmeta_get_provider_id(STATE->provider) !=
                    IPMETA_PROVIDER_MEMCACHE_PSQL) {
        fprintf(stderr,
                "ERROR: Only IPInfo-compliant providers (ipinfo, memcache_psql) are currently supported\n");
        return -1;
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

static void clear_iso2_map(khash_t(iso2_map) *map) {
    khint_t k;
    per_geo_t *pg;

    for (k = kh_begin(map); k != kh_end(map); ++k) {
        if (!kh_exist(map, k)) {
            continue;
        }
        pg = (per_geo_t *)kh_value(map, k);
        per_geo_destroy(pg);
    }

    kh_destroy(iso2_map, map);
}

static void clear_name_map(khash_t(name_map) *map) {
    khint_t k;
    per_geo_t *pg;

    for (k = kh_begin(map); k != kh_end(map); ++k) {
        if (!kh_exist(map, k)) {
            continue;
        }
        pg = (per_geo_t *)kh_value(map, k);
        per_geo_destroy(pg);
    }

    kh_destroy(name_map, map);
}

static void clear_iso2_runs(khash_t(iso2_runs) *map) {
    khint_t k;
    pfx_location_t *loc;

    for (k = kh_begin(map); k != kh_end(map); ++k) {
        if (!kh_exist(map, k)) {
            continue;
        }
        loc = (pfx_location_t *)kh_value(map, k);
        bgpstream_ipv6_pfx_set_destroy(loc->addr6_pfxs);
        free(loc->addr_runs);
        free(loc);
    }
    kh_destroy(iso2_runs, map);
}

static void clear_name_runs(khash_t(name_runs) *map) {
    khint_t k;
    pfx_location_t *loc;

    for (k = kh_begin(map); k != kh_end(map); ++k) {
        if (!kh_exist(map, k)) {
            continue;
        }
        loc = (pfx_location_t *)kh_value(map, k);
        bgpstream_ipv6_pfx_set_destroy(loc->addr6_pfxs);
        free(loc->addr_runs);
        free(loc);
    }
    kh_destroy(name_runs, map);
}

static void destroy_ipmeta(bvc_t *consumer) {
    int i, j;

    /* empty continents, countries, regions, cities maps */
    clear_iso2_map(STATE->continents);
    clear_iso2_map(STATE->countries);
    clear_name_map(STATE->regions);
    clear_name_map(STATE->cities);

    if (STATE->ipmeta != NULL) {
        ipmeta_free(STATE->ipmeta);
        STATE->ipmeta = NULL;
    }

    if (STATE->records != NULL) {
        ipmeta_record_set_free(&STATE->records);
        STATE->records = NULL;
    }
}

static int reload_ipmeta(bvc_t *consumer, bgpview_t *view) {

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
    return 0;
}

static void destroy_pfx_user_ptr(void *user) {
    perpfx_cache_t *pfx_cache = (perpfx_cache_t *)user;

    clear_iso2_runs(pfx_cache->continents);
    clear_iso2_runs(pfx_cache->countries);
    clear_name_runs(pfx_cache->regions);
    clear_name_runs(pfx_cache->cities);

    free(pfx_cache);
}

static int clear_geocache(bvc_t *consumer, bgpview_t *view) {
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

static void init_name_map(khash_t(name_map) *map, const char **names) {

    int i, ret;
    per_geo_t *pg;
    khint_t k;

    for (i = 0; i < ARR_CNT(names); i++) {
        k = kh_put(name_map, map, names[i], &ret);
        if (ret == 0) {
            fprintf(stderr, "WARNING: duplicate geolocation name: %s\n",
                    names[i]);
            continue;
        }
        pg = calloc(1, sizeof(per_geo_t));
        METRIC_PREFIX_INIT(pg, METRIC_PATH, names[i]);

        kh_value(map, k) = pg;
    }
}

static void init_iso2_map(khash_t(iso2_map) *map, const char **iso2codes) {

    int i, len, ret;
    per_geo_t *pg;
    char *ptr;
    khint_t k;

    for (i = 0; i < ARR_CNT(iso2codes); i++) {
        uint16_t key;
        len = strlen(iso2codes[i]);

        if (len < 2) {
            continue;
        } else {
            ptr = iso2codes[i] + (len - 2);
            key = CC_16(ptr);
        }

        k = kh_put(iso2_map, map, key, &ret);
        if (ret == 0) {
            fprintf(stderr, "WARNING: duplicate geolocation name: %s\n",
                    iso2codes[i]);
            continue;
        }
        pg = calloc(1, sizeof(per_geo_t));
        METRIC_PREFIX_INIT(pg, METRIC_PATH, iso2codes[i]);

        kh_value(map, k) = pg;
    }
}

static int create_geo_pfxs_vis(bvc_t *consumer) {

    int country_cnt = 0, i;
    const char **countries_iso2 = NULL;
    const char **country_continents = NULL;

    const char **country_strings = NULL;

    STATE->continents = kh_init(iso2_map);
    STATE->countries = kh_init(iso2_map);
    STATE->regions = kh_init(name_map);
    STATE->cities = kh_init(name_map);

    /* TODO insert initialized per_geo_t entries for each known
     * continent, region, country...
     */
    init_iso2_map(STATE->continents, continent_strings);

    country_cnt = ipmeta_provider_maxmind_get_iso2_list(&countries_iso2);
    if (ipmeta_provider_maxmind_get_country_continent_list(&country_continents) != country_cnt) {
        fprintf(stderr, "ERROR: not all ISO2 country codes in libipmeta have a corresponding continent code?\n");
        return -1;
    }

    country_strings = calloc(country_cnt, sizeof(char *));

    for (i = 0; i < country_cnt; i++) {
        char newstr[32];
        snprintf(newstr, 32, "%s.%s", country_continents[i], countries_iso2[i]);

        country_strings[i] = (const char *)strdup(newstr);
    }

    init_iso2_map(STATE->countries, country_strings);

    for (i = 0; i < country_cnt; i++) {
        free(country_strings[i]);
    }
    free(country_strings);
    return 0;
}

static pfx_location_t *lookup_iso2(khash_t(iso2_runs) **map,
        const char *iso2) {

    uint16_t cont_idx;
    khint_t k;
    int ret;
    pfx_location_t *loc = NULL;

    if (*iso2 == '\0') {
        cont_idx = 0x3F3F;
    } else {
        cont_idx = CC_16(iso2);
    }

    k = kh_get(iso2_runs, *map, cont_idx);
    if (k == kh_end(*map)) {
        k = kh_put(iso2_runs, *map, cont_idx, &ret);
        loc = calloc(1, sizeof(pfx_location_t));

        kh_value(*map, k) = loc;
    } else {
        loc = kh_value(*map, k);
    }

    return loc;
}

static pfx_location_t *lookup_named(khash_t(iso2_runs) **map,
        const char *name) {

    khint_t k;
    int ret;
    pfx_location_t *loc = NULL;

    if (*iso2 == '\0') {
        return NULL;
    }

    k = kh_get(name_runs, *map, name);
    if (k == kh_end(*map)) {
        k = kh_put(name_runs, *map, name, &ret);
        loc = calloc(1, sizeof(pfx_location_t));

        kh_value(*map, k) = loc;
    } else {
        loc = kh_value(*map, k);
    }

    return loc;
}

static int update_pfx(bvc_t *consumer, bgpstream_pfx_t *pfx,
                perpfx_cache_t *pfx_cache, uint64_t *iptally) {
    uint64_t num_ips = 0;
    uint64_t cur_address = first_pfx_addr(pfx);
    ipmeta_record_t *rec = NULL;
    int poly_table;

    /* Perform lookup */
    ipmeta_record_set_clear(STATE->records);

    if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV6) {
        ipmeta_lookup_pfx(STATE->ipmeta, AF_INET6,
                (void *)(&(pfx->address.bs_ipv6.addr.s6_addr)),
                pfx->mask_len, 0, STATE->records);
    } else if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
         ipmeta_lookup_pfx(STATE->ipmeta, AF_INET,
                (void *)(&(pfx->address.bs_ipv4.addr.s_addr)),
                pfx->mask_len, 0, STATE->records);
    } else {
        return 0;
    }

    ipmeta_record_set_rewind(STATE->records);

    while ((rec = ipmeta_record_set_next(STATE->records, &num_ips))) {
        pfx_location_t *loc;

        /* continent */
        loc = lookup_iso2(&(pfx_cache->continents),
                (const char *)rec->continent_code);
        if (loc != NULL) {
            if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV6 &&
                    update_ip6_prefix(loc, cur_addr, num_ips) == NULL) {
                return -1;
            } else if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4 &&
                    update_ip_addr_run(loc, cur_addr, num_ips) == NULL) {
                return -1;
            }
        }

        /* country */
        loc = lookup_iso2(&(pfx_cache->countries),
                (const char *)rec->country_code);
        if (loc != NULL) {
            if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV6 &&
                    update_ip6_prefix(loc, cur_addr, num_ips) == NULL) {
                return -1;
            } else if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4 &&
                    update_ip_addr_run(loc, cur_addr, num_ips) == NULL) {
                return -1;
            }
        }

        /* TODO */

        /* region */

        /* city */

        cur_addr += num_ips;
        (*iptally) += num_ips;

    }
    return 0;
}

static int update_pfx_geo_named(bvc_t *consumer, khash_t(name_map) *aggs,
        khash_t(name_runs) *cached, bgpstream_pfx_t *pfx) {

    per_geo_t *pg;
    pfx_location_t *loc;
    khint_t k, k2;

    for (k = kh_begin(cached); k != kh_end(cached); ++k) {

        if (!kh_exist(cached, k)) {
            continue;
        }
        loc = (pfx_location_t *)kh_value(cached, k);

        k2 = kh_get(name_map, aggs, kh_key(cached, k));

        if (k2 == kh_end(aggs)) {
            fprintf(stderr, "ERROR: Named location %04x is present in pfx_cache, but not in main aggregation map?\n", kh_key(cached, k));
            return -1;
        }

        pg = (per_geo_t *)kh_value(aggs, k2);

        if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
            if (per_geo_update(consumer, pg, pfx, loc) != 0) {
                return -1;
            }
        } else {
            if (per_geo_update_v6(consumer, pg, pfx, loc) != 0) {
                return -1;
            }
        }
    }

    return 0;
}

static int update_pfx_geo_iso2(bvc_t *consumer, khash_t(iso2_map) *aggs,
        khash_t(iso2_runs) *cached, bgpstream_pfx_t *pfx) {

    per_geo_t *pg;
    pfx_location_t *loc;
    khint_t k, k2;

    for (k = kh_begin(cached); k != kh_end(cached); ++k) {

        if (!kh_exist(cached, k)) {
            continue;
        }
        loc = (pfx_location_t *)kh_value(cached, k);

        k2 = kh_get(iso2_map, aggs, kh_key(cached, k));

        if (k2 == kh_end(aggs)) {
            fprintf(stderr, "ERROR: ISO2 code %04x is present in pfx_cache, but not in main aggregation map?\n", kh_key(cached, k));
            return -1;
        }

        pg = (per_geo_t *)kh_value(aggs, k2);

        if (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) {
            if (per_geo_update(consumer, pg, pfx, loc) != 0) {
                return -1;
            }
        } else {
            if (per_geo_update_v6(consumer, pg, pfx, loc) != 0) {
                return -1;
            }
        }
    }

    return 0;
}

static int update_pfx_geo_information(bvc_t *consumer, bgpview_iter_t *it) {
    bgpstream_pfx_t *pfx = bgpview_iter_pfx_get_pfx(it);
    perpfx_cache_t *pfx_cache = (perpfx_cache_t *)bgpview_iter_pfx_get_user(it);

    uint64_t num_ips = 0;
    uint64_t cur_address = first_pfx_addr(pfx);
    ipmeta_record_t *rec = NULL;

    int r;

    /* if the user pointer (cache) does not exist, then do the lookup now */
    if (pfx_cache == NULL) {
        if ((pfx_cache = malloc_zero(sizeof(perpfx_cache_t))) == NULL) {
            fprintf(stderr, "Error: cannot create per-pfx cache\n");
            return -1;
        }

        pfx_cache->continents = kh_init(iso2_runs);
        pfx_cache->countries = kh_init(iso2_runs);
        pfx_cache->regions = kh_init(name_runs);
        pfx_cache->cities = kh_init(name_runs);

        if ((r = update_pfx(consumer, pfx, pfx_cache, &num_ips)) < 0) {
            return -1;
        }
        if (r == 0) {
            return 0;
        }

        /* link the cache to the appropriate user ptr */
        bgpview_iter_pfx_set_user(it, pfx_cache);
    }
    /* now the prefix cache holds geo info we can update the counters for each
     * aggregate (continents, countries, polygons)  TODO */

    /* continents */
    if (update_pfx_geo_iso2(consumer, STATE->continents, pfx_cache->continents,
            pfx) < 0) {
        return -1;
    }

    /* countries */
    if (update_pfx_geo_iso2(consumer, STATE->countries, pfx_cache->countries,
            pfx) < 0) {
        return -1;
    }

    /* regions */

    /* cities */

    return 0;
}


static int compute_geo_pfx_visibility(bvc_t *consumer, bgpview_iter_t *it) {
    bgpstream_pfx_t *pfx;
    bgpstream_peer_sig_t *sg;

    /* for each prefix in the view */
    for (bgpview_iter_first_pfx(it, 0, BGPVIEW_FIELD_ACTIVE); //
            bgpview_iter_has_more_pfx(it);                //
            bgpview_iter_next_pfx(it)) {

        pfx = bgpview_iter_pfx_get_pfx(it);

        /* only consider if the (ipv4) prefix mask is longer than a /6 */
        if (pfx->mask_len <
                BVC_GET_CHAIN_STATE(consumer)->pfx_vis_mask_len_threshold) {
            continue;
        }

        /* reset information for the current prefix */
        bgpstream_id_set_clear(STATE->ff_asns);
        STATE->valid_origins = 0;

        /* iterate over the peers for the current pfx and get the number of
         * unique full feed AS numbers observing this prefix as well as the
         * unique set of origin ASes */
        for (bgpview_iter_pfx_first_peer(it, BGPVIEW_FIELD_ACTIVE); //
                bgpview_iter_pfx_has_more_peer(it);                    //
                bgpview_iter_pfx_next_peer(it)) {

            /* only consider peers that are full-feed (checking if peer id is
             * a full feed for the current pfx IP version) */
            if (bgpstream_id_set_exists(
                        BVC_GET_CHAIN_STATE(consumer)->full_feed_peer_ids[bgpstream_ipv2idx(pfx->address.version)],
                        bgpview_iter_peer_get_peer_id(it)) == 0) {
                continue;
            }

            /* get peer signature */
            sg = bgpview_iter_peer_get_sig(it);
            assert(sg != NULL);

            /* Add peer AS number to set of full feed peers observing the
             * prefix */
            bgpstream_id_set_insert(STATE->ff_asns, sg->peer_asnumber);

            /* Add origin AS number to the array of origin ASNs */
            add_origin(STATE, bgpview_iter_pfx_peer_get_origin_seg(it));
        }

        if (STATE->valid_origins > 0 &&
                update_pfx_geo_information(consumer, it) != 0) {
            return -1;
        }
    }

    return 0;
}

static int update_per_geo_metrics(bvc_t *consumer, per_geo_t *pg)
{
    int i;
    int v4ind, v6ind;
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

        /* now that the tree represents all the prefixes that match the
         * threshold, we extract the information that we want to output */

        v4ind = bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4);
        v6ind = bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV6);

        /* IPv4*/
        timeseries_kp_set(
                STATE->kp, pg->thresholds[i].pfx_cnt_idx[v4ind],
                bgpstream_patricia_prefix_count(pg->thresholds[i].pfxs,
                    BGPSTREAM_ADDR_VERSION_IPV4));

        timeseries_kp_set(
                STATE->kp,
                pg->thresholds[i].subnet_cnt_idx[v4ind],
                slash24_id_set_size(pg->thresholds[i].slash24s));

        timeseries_kp_set(
                STATE->kp,
                pg->thresholds[i].asns_cnt_idx[v4ind],
                bgpstream_id_set_size(pg->thresholds[i].asns));

        /* IPv6 */
        timeseries_kp_set(
                STATE->kp, pg->thresholds[i].pfx_cnt_idx[v6ind],
                bgpstream_patricia_prefix_count(pg->thresholds[i].pfxs,
                    BGPSTREAM_ADDR_VERSION_IPV6));

        timeseries_kp_set(
                STATE->kp,
                pg->thresholds[i].subnet_cnt_idx[v6ind],
                bgpstream_patricia_tree_count_64subnets(
                        pg->thresholds[i].v6_subnets));

        timeseries_kp_set(
                STATE->kp,
                pg->thresholds[i].asns_cnt_idx[v6ind],
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

static int update_metrics_iso2(bvc_t *consumer, khash_t(iso2_map) *map) {
    khint_t k;
    per_geo_t *pg;

    for (k = kh_begin(map); k != kh_end(map); ++k) {
        if (!kh_exist(map, k)) {
            continue;
        }
        pg = (per_geo_t *)kh_value(map, k);
        if (update_per_geo_metrics(consumer, pg) < 0) {
            return -1;
        }
    }
    return 0;
}

static int update_metrics(bvc_t *consumer) {

    /* for each continent */
    if (update_metrics_iso2(consumer, STATE->continents) < 0) {
        return -1;
    }

    /* for each country */
    if (update_metrics_iso2(consumer, STATE->countries) < 0) {
        return -1;
    }

    /* for each region */
    /* TODO iterate over STATE->regions and update_per_geo_metrics() */

    /* for each city */
    /* TODO iterate over STATE->cities and update_per_geo_metrics() */

    return 0;
}


/* ==================== CONSUMER INTERFACE FUNCTIONS ==================== */

bvc_t *bvc_pergeovisibility_ipinfo_alloc() {
    return &bvc_pergeovisibility_ipinfo;
}

int bvc_pergeovisibility_ipinfo_init(bvc_t *consumer, int argc, char **argv) {
    bvc_pergeovisibility_ipinfo_state_t *state = NULL;

    if ((state = malloc_zero(sizeof(bvc_pergeovisibility_info_state_t))) ==
            NULL) {
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
                "ERROR: The Per-Geo Visibility requires the Visibility "
                "consumer to be run first\n");
        goto err;
    }

    return 0;

err:
    bvc_pergeovisibility_ipinfo_destroy(consumer);
    return -1;
}

void bvc_pergeovisibility_ipinfo_destroy(bvc_t *consumer) {
{
    if (STATE == NULL) {
        return;
    }

    destroy_ipmeta(consumer);

    free(STATE->provider_config);
    STATE->provider_config = NULL;
    STATE->provider_name = NULL;
    STATE->provider_arg = NULL;

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
    int idx = bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4);

    /* set the pfx user pointer destructor function */
    bgpview_set_pfx_user_destructor(view, destroy_pfx_user_ptr);

    if (STATE->last_reload == 0) {
        STATE->last_reload = bgpview_get_time(view);
    }

    /* should we reload the ipmeta instance? (to pick up a new database) */
    if (STATE->reload_freq > 0 &&
            strcmp(STATE->provider_name, "memcache_psql") != 0 &&
            bgpview_get_time(view) >= (STATE->last_reload +
                    STATE->reload_freq)) {

        if (reload_ipmeta(consumer, view) == -1) {
            return -1;
        }
    }

    if (BVC_GET_CHAIN_STATE(consumer)->usable_table_flag[idx] == 0) {
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

