/*
# This source code is Copyright (c) Georgia Tech Research Corporation. All
# Rights Reserved. Permission to copy, modify, and distribute this software and
# its documentation for academic research and education purposes, without fee,
# and without a written agreement is hereby granted, provided that the above
# copyright notice, this paragraph and the following three paragraphs appear in
# all copies. Permission to make use of this software for other than academic
# research and education purposes may be obtained by contacting:
#
#  Office of Technology Licensing
#  Georgia Institute of Technology
#  926 Dalney Street, NW
#  Atlanta, GA 30318
#  404.385.8066
#  techlicensing@gtrc.gatech.edu
#
# This software program and documentation are copyrighted by Georgia Tech
# Research Corporation (GTRC). The software program and documentation are 
# supplied "as is", without any accompanying services from GTRC. GTRC does
# not warrant that the operation of the program will be uninterrupted or
# error-free. The end-user understands that the program was developed for
# research purposes and is advised not to rely exclusively on the program for
# any reason.
#
# IN NO EVENT SHALL GEORGIA TECH RESEARCH CORPORATION BE LIABLE TO ANY PARTY FOR
# DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING
# LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION,
# EVEN IF GEORGIA TECH RESEARCH CORPORATION HAS BEEN ADVISED OF THE POSSIBILITY
# OF SUCH DAMAGE. GEORGIA TECH RESEARCH CORPORATION SPECIFICALLY DISCLAIMS ANY
# WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED
# HEREUNDER IS ON AN "AS IS" BASIS, AND  GEORGIA TECH RESEARCH CORPORATION HAS
# NO OBLIGATIONS TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
# MODIFICATIONS.
*/

/*
 *
 * This code is part of bgpview. The original bgpview software is
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

#include "bvc_pathinfo.h"
#include "bgpview_consumer_interface.h"
#include "bgpview_consumer_utils.h"
#include "utils.h"
#include "libipmeta.h"
#include <wandio.h>
#include <assert.h>
#include <fcntl.h>
#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#define NAME "pathinfo"

#define STATE (BVC_GET_STATE(consumer, pathinfo))

/* Our 'class' structure */
static bvc_t bvc_pathinfo = {BVC_ID_PATHINFO, NAME, BVC_GENERATE_PTRS(pathinfo)};

/* Allocation state structure */
typedef struct bvc_pathinfo_state {
  /** Output file writer using wandio */
  iow_t *outfile;
  char *outfile_pattern;
  int outfile_compress;

  /** libipmeta structures */
  ipmeta_t *ipmeta;
  ipmeta_provider_t *provider;
  ipmeta_record_set_t *records;

  char *provider_name;
  char *provider_config;
} bvc_pathinfo_state_t;

/* Helper to append strings for file template expansion */
#define stradd(str, bufp, buflim)                                              \
  do {                                                                         \
    char *strp = str;                                                          \
    while (bufp < buflim && (*bufp = *strp++) != '\0')                         \
      ++bufp;                                                                  \
  } while (0)

/* Generate output filename from pattern and view timestamp */
static char *generate_file_name(const char *template, uint32_t time)
{
  char buf[1024];
  char tbuf[1024];
  char *bufp = buf;
  char *buflim = buf + sizeof(buf);

  const char *tmpl = template;
  char secs[11]; /* length of UINT32_MAX +1 */
  time_t epoch_sec = time;

  for (; *tmpl; ++tmpl) {
    if (*tmpl == '%') {
      switch (*++tmpl) {
      case '\0':
        --tmpl;
        break;

      case 's': /* unix timestamp */
        snprintf(secs, sizeof(secs), "%" PRIu32, time);
        stradd(secs, bufp, buflim);
        continue;

      default:
        /* leave non-recognized formats intact for strftime to use */
        --tmpl;
      }
    }
    if (bufp == buflim)
      break;
    *bufp++ = *tmpl;
  }

  *bufp = '\0';

  /* Format via strftime in UTC */
  strftime(tbuf, sizeof(tbuf), buf, gmtime(&epoch_sec));
  return strdup(tbuf);
}

/* Print usage information to stderr */
static void usage(bvc_t *consumer)
{
  fprintf(stderr,
          "consumer usage: %s\n"
          "       -o <output-pattern>   output file pattern (default: stdout, supports strftime formats and %%s)\n"
          "       -p <provider-name>    ipmeta provider name (default: \"ipinfo\")\n"
          "       -g <provider-config>  ipmeta provider configuration (e.g. database path)\n",
          consumer->name);
}

/* Parse command line arguments */
static int parse_args(bvc_t *consumer, int argc, char **argv)
{
  int opt;
  bvc_pathinfo_state_t *state = STATE;

  /* Reset getopt's external state */
  optind = 1;

  while ((opt = getopt(argc, argv, ":o:c:p:g:?")) >= 0) {
    switch (opt) {
    case 'c':
      state->outfile_compress = atoi(optarg);
      break;
    case 'o':
      if (state->outfile_pattern != NULL) {
        free(state->outfile_pattern);
      }
      state->outfile_pattern = strdup(optarg);
      break;
    case 'p':
      if (state->provider_name != NULL) {
        free(state->provider_name);
      }
      state->provider_name = strdup(optarg);
      break;
    case 'g':
      if (state->provider_config != NULL) {
        free(state->provider_config);
      }
      state->provider_config = strdup(optarg);
      break;
    case '?':
    case ':':
    default:
      usage(consumer);
      return -1;
    }
  }

  /* Ensure provider_config is set since geolocation lookup is required */
  if (state->provider_config == NULL) {
    fprintf(stderr, "Error: ipmeta provider configuration path (-g) is required.\n");
    usage(consumer);
    return -1;
  }

  return 0;
}

/* Initialize ipmeta and local provider */
static int init_ipmeta(bvc_t *consumer)
{
  bvc_pathinfo_state_t *state = STATE;

  if ((state->ipmeta = ipmeta_init(IPMETA_DS_PATRICIA)) == NULL) {
    fprintf(stderr, "Error: Could not initialize ipmeta\n");
    return -1;
  }

  if ((state->provider = ipmeta_get_provider_by_name(state->ipmeta, state->provider_name)) == NULL) {
    fprintf(stderr, "Error: Could not retrieve ipmeta provider '%s'\n", state->provider_name);
    return -1;
  }

  if (ipmeta_enable_provider(state->ipmeta, state->provider, state->provider_config) != 0) {
    fprintf(stderr, "Error: Could not enable ipmeta provider with config '%s'\n", state->provider_config);
    return -1;
  }

  if ((state->records = ipmeta_record_set_init()) == NULL) {
    fprintf(stderr, "Error: Could not initialize ipmeta record set\n");
    return -1;
  }

  return 0;
}

/* Cleanup ipmeta allocations */
static void destroy_ipmeta(bvc_t *consumer)
{
  bvc_pathinfo_state_t *state = STATE;

  if (state->records != NULL) {
    ipmeta_record_set_free(&state->records);
    state->records = NULL;
  }

  if (state->ipmeta != NULL) {
    ipmeta_free(state->ipmeta);
    state->ipmeta = NULL;
  }
}

/* ==================== CONSUMER INTERFACE FUNCTIONS ==================== */

bvc_t *bvc_pathinfo_alloc(void)
{
  return &bvc_pathinfo;
}

int bvc_pathinfo_init(bvc_t *consumer, int argc, char **argv)
{
  bvc_pathinfo_state_t *state = NULL;

  if ((state = malloc_zero(sizeof(bvc_pathinfo_state_t))) == NULL) {
    return -1;
  }
  BVC_SET_STATE(consumer, state);

  /* Set defaults */
  state->outfile = NULL;
  state->outfile_pattern = NULL;
  state->outfile_compress = BVCU_DEFAULT_COMPRESS_LEVEL;
  state->provider_name = strdup("ipinfo");
  state->provider_config = NULL;
  state->ipmeta = NULL;
  state->provider = NULL;
  state->records = NULL;

  /* Parse command line arguments */
  if (parse_args(consumer, argc, argv) != 0) {
    goto err;
  }

  /* Set output default if not specified */
  if (state->outfile_pattern == NULL) {
    state->outfile_pattern = strdup("-");
  }

  /* Initialize ipmeta */
  if (init_ipmeta(consumer) != 0) {
    goto err;
  }

  return 0;

err:
  bvc_pathinfo_destroy(consumer);
  return -1;
}

void bvc_pathinfo_destroy(bvc_t *consumer)
{
  bvc_pathinfo_state_t *state = STATE;

  if (state != NULL) {
    destroy_ipmeta(consumer);

    if (state->outfile != NULL) {
      wandio_wdestroy(state->outfile);
      state->outfile = NULL;
    }

    if (state->outfile_pattern != NULL) {
      free(state->outfile_pattern);
    }
    if (state->provider_name != NULL) {
      free(state->provider_name);
    }
    if (state->provider_config != NULL) {
      free(state->provider_config);
    }

    free(state);
    BVC_SET_STATE(consumer, NULL);
  }
}

int bvc_pathinfo_process_view(bvc_t *consumer, bgpview_t *view)
{
  bvc_pathinfo_state_t *state = STATE;
  bgpview_iter_t *it = NULL;
  uint32_t view_time = bgpview_get_time(view);
  char *actual_outfile = NULL;

  /* Open the output writer dynamically based on view timestamp */
  if (state->outfile_pattern != NULL && strcmp(state->outfile_pattern, "-") != 0) {
    actual_outfile = generate_file_name(state->outfile_pattern, view_time);
    int compress_type = wandio_detect_compression_type(actual_outfile);
    if ((state->outfile = wandio_wcreate(actual_outfile, compress_type, state->outfile_compress, O_CREAT)) == NULL) {
      fprintf(stderr, "Error: Could not open output file '%s' for writing\n", actual_outfile);
      free(actual_outfile);
      return -1;
    }
  } else if (state->outfile_compress > 0) {
    if ((state->outfile = wandio_wcreate("-", WANDIO_COMPRESS_ZLIB, state->outfile_compress, O_CREAT)) == NULL) {
      fprintf(stderr, "Error: Could not open stdout for writing\n");
      return -1;
    }
  } else {
    /* Write to stdout if no file is specified or if '-' is passed */
    if ((state->outfile = wandio_wcreate("-", WANDIO_COMPRESS_NONE, 0, O_CREAT)) == NULL) {
      fprintf(stderr, "Error: Could not open stdout for writing\n");
      return -1;
    }
  }

  if ((it = bgpview_iter_create(view)) == NULL) {
    if (actual_outfile != NULL) {
      wandio_wdestroy(state->outfile);
      state->outfile = NULL;
      free(actual_outfile);
    }
    return -1;
  }

  fprintf(stderr, "DEBUG: Active V4: %" PRIu32 ", Inactive V4: %" PRIu32 ", Active V6: %" PRIu32 ", Inactive V6: %" PRIu32 "\n",
          bgpview_v4pfx_cnt(view, BGPVIEW_FIELD_ACTIVE),
          bgpview_v4pfx_cnt(view, BGPVIEW_FIELD_INACTIVE),
          bgpview_v6pfx_cnt(view, BGPVIEW_FIELD_ACTIVE),
          bgpview_v6pfx_cnt(view, BGPVIEW_FIELD_INACTIVE));

  /* Iterate over all active prefixes in the BGP view */
  for (bgpview_iter_first_pfx(it, 0, BGPVIEW_FIELD_ACTIVE);
       bgpview_iter_has_more_pfx(it);
       bgpview_iter_next_pfx(it))
  {
    bgpstream_pfx_t *pfx = bgpview_iter_pfx_get_pfx(it);
    char pfx_str[INET6_ADDRSTRLEN + 3];
    bgpstream_pfx_snprintf(pfx_str, sizeof(pfx_str), pfx);

    /* Geolocation lookup using libipmeta */
    const char *country = "--";
    const char *region = "--";
    
    ipmeta_record_set_clear(state->records);
    int family = (pfx->address.version == BGPSTREAM_ADDR_VERSION_IPV4) ? AF_INET : AF_INET6;
    void *addr_ptr = (family == AF_INET) ? 
        (void *)(&(pfx->address.bs_ipv4.addr.s_addr)) : 
        (void *)(&(pfx->address.bs_ipv6.addr.s6_addr));

    ipmeta_lookup_pfx(state->ipmeta, family, addr_ptr, pfx->mask_len, 0, state->records);
    ipmeta_record_set_rewind(state->records);
    
    uint64_t num_ips = 0;
    ipmeta_record_t *rec = ipmeta_record_set_next(state->records, &num_ips);
    if (rec != NULL) {
      if (rec->country_code[0] != '\0') {
        country = rec->country_code;
      }
      if (rec->region != NULL && rec->region[0] != '\0') {
        region = rec->region;
      }
    }

    /* Iterate over each peer announcing the active prefix */
    for (bgpview_iter_pfx_first_peer(it, BGPVIEW_FIELD_ACTIVE);
         bgpview_iter_pfx_has_more_peer(it);
         bgpview_iter_pfx_next_peer(it))
    {
      bgpstream_peer_sig_t *ps = bgpview_iter_peer_get_sig(it);
      char peer_ip_str[INET6_ADDRSTRLEN];
      bgpstream_addr_ntop(peer_ip_str, sizeof(peer_ip_str), &ps->peer_ip_addr);

      /* Get destination (origin) ASN */
      bgpstream_as_path_seg_t *origin_seg = bgpview_iter_pfx_peer_get_origin_seg(it);
      uint32_t dest_asn = 0;
      if (origin_seg != NULL && origin_seg->type == BGPSTREAM_AS_PATH_SEG_ASN) {
        dest_asn = ((bgpstream_as_path_seg_asn_t *)origin_seg)->asn;
      }

      /* Get full AS path and format it as a string */
      bgpstream_as_path_t *path = bgpview_iter_pfx_peer_get_as_path(it);
      char path_str[4096] = "";
      if (path != NULL) {
        bgpstream_as_path_snprintf(path_str, sizeof(path_str), path);
        bgpstream_as_path_destroy(path);
      }

      /* Output quoted/comma-separated format:
       * "prefix","collector","peer",dest_asn,"country","region","full_as_path" */
      wandio_printf(state->outfile, "\"%s\",\"%s\",\"%s\",%" PRIu32 ",\"%s\",\"%s\",\"%s\"\n",
                    pfx_str, ps->collector_str, peer_ip_str, dest_asn, country, region, path_str);
    }
  }

  bgpview_iter_destroy(it);

  /* Clean up current view file handle */
  if (state->outfile != NULL) {
    wandio_wdestroy(state->outfile);
    state->outfile = NULL;
  }
  if (actual_outfile != NULL) {
    free(actual_outfile);
  }

  return 0;
}
