/*
 * This file is part of bgpstream
 *
 * CAIDA, UC San Diego
 * bgpstream-info@caida.org
 *
 * Copyright (C) 2012 The Regents of the University of California.
 * Authors: Alistair King, Chiara Orsini
 *
 * This program is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation; either version 2 of the License, or (at your option) any later
 * version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>

#include <czmq.h>

#include "utils.h"
#include "wandio_utils.h"
#include "khash.h"

#include "bgpstream_utils_pfx_set.h"
#include "bgpview_consumer_interface.h"
#include "bvc_announcedpfxs.h"


#define NAME                         "announced-pfxs"
#define CONSUMER_METRIC_PREFIX       "announced-pfxs"

#define BUFFER_LEN 1024
#define METRIC_PREFIX_TH_FORMAT    "%s."CONSUMER_METRIC_PREFIX".%"PRIu32"s-window.%s"
#define META_METRIC_PREFIX_FORMAT  "%s.meta.bgpview.consumer."NAME".%s"


/** Default size of window: 1 week (s) */
#define WINDOW_SIZE (7*24*3600)
/** Default output interval: 1 day (s) */
#define OUTPUT_INTERVAL (24*3600)
/** Default minimum netmask lenght of admissible prefix */
#define MIN_PFX4_LEN 7
/** Default maximum netmask lenght of admissible prefix */
#define MAX_PFX4_LEN 24
/** Default compression level of output file */
#define DEFAULT_COMPRESS_LEVEL 6
/** Default permission for output folder */
#define FOLDER_PERMISSION_MODE (S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH)


#define STATE					\
  (BVC_GET_STATE(consumer, announcedpfxs))

#define CHAIN_STATE                             \
  (BVC_GET_CHAIN_STATE(consumer))


/* our 'class' */
static bvc_t bvc_announcedpfxs = {
  BVC_ID_ANNOUNCEDPFXS,
  NAME,
  BVC_GENERATE_PTRS(announcedpfxs)
};


/** Map <ipv4-prefix,last_ts>
 */
KHASH_INIT(bwv_v4pfx_timestamp,
           bgpstream_ipv4_pfx_t,
           uint32_t, 1,
           bgpstream_ipv4_pfx_storage_hash_val,
           bgpstream_ipv4_pfx_storage_equal_val);
typedef khash_t(bwv_v4pfx_timestamp) bwv_v4pfx_timestamp_t;


/* our 'instance' */
typedef struct bvc_announcedpfxs_state {

  /** ts when the view arrived */
  uint32_t arrival_delay;
  /** ts when the view processing finished */
  uint32_t processed_delay;
  /** processing time */
  uint32_t processing_time;
  
  /** window size: i.e. for how long a prefix
   *  is considered "announced"  */
  uint32_t window_size;
  
  /** output interval: how frequently the plugin
   *  output prefixes*/
  uint32_t out_interval;

  /** next time prefixes are going to be
   *  printed on file */
  uint32_t next_output_time;

  /** output folder */
  char output_folder[BUFFER_LEN];

  /* map prefix last seen timestamp pointer */
  bwv_v4pfx_timestamp_t *v4pfx_ts;

  /** Timeseries Key Package */
  timeseries_kp_t *kp;

  /** Metrics indices */
  int arrival_delay_idx;
  int processed_delay_idx;
  int processing_time_idx;
  int ipv4_visible_pfxs_count_idx;
  
} bvc_announcedpfxs_state_t;


/** Recursively create directories and subdirectories */
static int rec_mkdir(const char *dir) {

  if(dir == NULL)
    {
      return -1;
    }
  
  char file_path[PATH_MAX];
  int ret = snprintf(file_path, PATH_MAX,"%s",dir);
  file_path[PATH_MAX-1] = '\0';
  if(ret >= PATH_MAX || ret < 0)
    {
      fprintf(stderr, "ERROR: invalid folder %s\n", file_path);
    }
  
  char* i = &file_path[0];
  char* p = strchr(i, '/');
  while(p != NULL)
    {
      /* if not root */
      if(p != &file_path[0])
        {
          *p='\0';
          errno = 0;
          if(mkdir(file_path, FOLDER_PERMISSION_MODE) == -1)
            {
              if (errno != EEXIST)
                {
                  fprintf(stderr, "ERROR: could not create folder %s (%s)\n", file_path, dir);
                  perror("rec_mkdir");                         
                  return -1;
                }
            }
          *p='/';                
        }
      
      i = p+1;      
      p = strchr(i, '/');
    }

  /* printing the last part of the path */
  if(*i != '\0')
    {
      errno = 0;
      if(mkdir(file_path, FOLDER_PERMISSION_MODE) == -1)
        {
          if (errno != EEXIST)
            {
              fprintf(stderr, "ERROR: could not create folder %s (%s)\n", file_path, dir);
              perror("rec_mkdir");                         
              return -1;
            }
        }          
    }

  return 0;
}

/** Create timeseries metrics */

static int create_ts_metrics(bvc_t *consumer)
{

  char buffer[BUFFER_LEN];
  bvc_announcedpfxs_state_t *state = STATE;

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "arrival_delay");             
  if((state->arrival_delay_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }
  
  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "processed_delay");             
  if((state->processed_delay_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "processing_time");             
  if((state->processing_time_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, METRIC_PREFIX_TH_FORMAT,
           CHAIN_STATE->metric_prefix, state->window_size, "v4pfx_count");             
  if((state->ipv4_visible_pfxs_count_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  return 0;
}


/** Print usage information to stderr */
static void usage(bvc_t *consumer)
{
  fprintf(stderr,
	  "consumer usage: %s\n"
	  "       -w <window-size>      window size in seconds (default %d)\n"
	  "       -i <output-interval>  output interval in seconds (default %d)\n"
	  "       -o <path>             output folder (default: current folder)\n",
	  consumer->name,
          WINDOW_SIZE,
          OUTPUT_INTERVAL);
}

/** Parse the arguments given to the consumer */
static int parse_args(bvc_t *consumer, int argc, char **argv)
{
  int opt;
  assert(argc > 0 && argv != NULL);

  bvc_announcedpfxs_state_t *state = STATE;

  /* NB: remember to reset optind to 1 before using getopt! */
  optind = 1;

  /* remember the argv strings DO NOT belong to us */
  while((opt = getopt(argc, argv, ":w:i:o:?")) >= 0)
    {
      switch(opt)
        {
        case 'w':
          state->window_size = strtoul(optarg, NULL, 10);
          break;
        case 'i':
          state->out_interval = strtoul(optarg, NULL, 10);
          break;
        case 'o':
          strncpy(state->output_folder, optarg, BUFFER_LEN-1);
          state->output_folder[BUFFER_LEN-1] = '\0';
          break;
        case '?':
        case ':':
        default:
          usage(consumer);
          return -1;
        }
    }

  return 0;
}


/* ==================== CONSUMER INTERFACE FUNCTIONS ==================== */

bvc_t *bvc_announcedpfxs_alloc()
{
  return &bvc_announcedpfxs;
}

int bvc_announcedpfxs_init(bvc_t *consumer, int argc, char **argv)
{
  bvc_announcedpfxs_state_t *state = NULL;

  if((state = malloc_zero(sizeof(bvc_announcedpfxs_state_t))) == NULL)
    {
      return -1;
    }
  BVC_SET_STATE(consumer, state);

  /* defaults here */
  state->window_size = WINDOW_SIZE;
  state->out_interval = OUTPUT_INTERVAL;
  strncpy(state->output_folder, "./", BUFFER_LEN);
  state->next_output_time = 0;
  state->v4pfx_ts = NULL;

  /* parse the command line args */
  if(parse_args(consumer, argc, argv) != 0)
    {
      goto err;
    }

  /* react to args here */
  fprintf(stderr, "INFO: window size: %"PRIu32"\n", state->window_size);
  fprintf(stderr, "INFO: output interval: %"PRIu32"\n", state->out_interval);
  fprintf(stderr, "INFO: output folder: %s\n", state->output_folder);
          

  /* create folder with read/write/search permissions for owner and group, 
   * and with read/search permissions for others */
  if(rec_mkdir(state->output_folder) != 0)
    {
          goto err;
    }
  
  /* init */
  if((state->v4pfx_ts = kh_init(bwv_v4pfx_timestamp)) == NULL)
    {
      goto err;
    }

  if((state->kp = timeseries_kp_init(BVC_GET_TIMESERIES(consumer), 1)) == NULL)
    {
      fprintf(stderr, "Error: Could not create timeseries key package\n");
      goto err;
    }
  
  if(create_ts_metrics(consumer) != 0)
    {
      goto err;
    }

  return 0;

 err:
  bvc_announcedpfxs_destroy(consumer);
  return -1;
}


void bvc_announcedpfxs_destroy(bvc_t *consumer)
{
  bvc_announcedpfxs_state_t *state = STATE;
  
  if(state != NULL)
    {
      if(state->v4pfx_ts != NULL)
        {
	  kh_destroy(bwv_v4pfx_timestamp,state->v4pfx_ts);
        }
      timeseries_kp_free(&state->kp);
      free(state);
      BVC_SET_STATE(consumer, NULL);
    }
}


int bvc_announcedpfxs_process_view(bvc_t *consumer, uint8_t interests,
				     bgpview_t *view)
{
  bvc_announcedpfxs_state_t *state = STATE;
  
  khiter_t k;
  int khret;

  uint32_t current_view_ts = bgpview_get_time(view);
  uint32_t last_valid_timestamp = current_view_ts - state->window_size;
  bgpview_iter_t *it;
  bgpstream_pfx_t *pfx;
  bgpstream_peer_id_t peerid;
  int ipv4_idx = bgpstream_ipv2idx(BGPSTREAM_ADDR_VERSION_IPV4);


  if((it = bgpview_iter_create(view)) == NULL)
    {
      return -1;
    }


  if(BVC_GET_CHAIN_STATE(consumer)->visibility_computed == 0)
    {
      fprintf(stderr,
              "ERROR: Announced-pfxs requires the Visibility consumer "
              "to be run first\n");
      return -1;
    }

  /* compute arrival delay */
  state->arrival_delay = zclock_time()/1000 - bgpview_get_time(view);

  /* iterate through ipv4 prefixes */
  for(bgpview_iter_first_pfx(it, BGPSTREAM_ADDR_VERSION_IPV4, BGPVIEW_FIELD_ACTIVE);
      bgpview_iter_has_more_pfx(it);
      bgpview_iter_next_pfx(it))
    {
      pfx = bgpview_iter_pfx_get_pfx(it);

      /* only consider ipv4 prefixes whose mask is within MIN and MAX LEN*/
      if(pfx->mask_len < MIN_PFX4_LEN || pfx->mask_len > MAX_PFX4_LEN)
        {
          continue;
        }

      if((k = kh_get(bwv_v4pfx_timestamp,state->v4pfx_ts,
                     * ((bgpstream_ipv4_pfx_t *) pfx))) == kh_end(state->v4pfx_ts))
        {
          /* new prefix */
          k = kh_put(bwv_v4pfx_timestamp,state->v4pfx_ts, *((bgpstream_ipv4_pfx_t *) pfx), &khret);
          kh_value(state->v4pfx_ts,k) = 0;
        }
      
      for(bgpview_iter_pfx_first_peer(it, BGPVIEW_FIELD_ACTIVE);
          bgpview_iter_pfx_has_more_peer(it);
          bgpview_iter_pfx_next_peer(it))
        {
          /* only consider peers that are full-feed */
          peerid = bgpview_iter_peer_get_peer_id(it);
          if(bgpstream_id_set_exists(BVC_GET_CHAIN_STATE(consumer)->full_feed_peer_ids[ipv4_idx], peerid))
            {
              /* update the prefix timestamp */
              kh_value(state->v4pfx_ts,k) = current_view_ts; 
              break;
            }
        }      
    }

  bgpview_iter_destroy(it);

  /* init next output time */
  if(state->next_output_time == 0)
    {
      state->next_output_time = current_view_ts + state->out_interval;
    }

  
  /* verify whether new information needs to be printed */
  if(state->next_output_time <= current_view_ts)
    {
      iow_t *f;
      char complete_folder[BUFFER_LEN];
      char date_sub[BUFFER_LEN];
      char filename[BUFFER_LEN];
      char buffer_str[BUFFER_LEN];
      time_t timestamp = current_view_ts;
      struct tm *p_time = gmtime(&timestamp);
      
      strftime(date_sub, sizeof(date_sub), "%Y/%m/%d", p_time);
      sprintf(complete_folder,"%s/%s", state->output_folder, date_sub);
      if(rec_mkdir(complete_folder) != 0)
        {
              return -1;
        }
      sprintf(filename,"%s/%"PRIu32"_w%"PRIu32"_prefixes.txt.gz", complete_folder, current_view_ts, state->window_size);

      /* open file for writing */
      if((f = wandio_wcreate(filename, wandio_detect_compression_type(filename), DEFAULT_COMPRESS_LEVEL, O_CREAT)) == NULL)
    	{
          fprintf(stderr, "ERROR: Could not open %s for writing\n",filename);
          return -1;
    	}

      /* prefix map iteration */
      for(k = kh_begin(state->v4pfx_ts); k < kh_end(state->v4pfx_ts); ++k)
        {
          if(kh_exist(state->v4pfx_ts, k))
            {
              /* print prefix if within the window */
              if(kh_value(state->v4pfx_ts,k) >= last_valid_timestamp)
                {
                  if(bgpstream_pfx_snprintf(buffer_str, INET6_ADDRSTRLEN+3,
                                            (bgpstream_pfx_t *) &kh_key(state->v4pfx_ts, k)) != NULL)
                    {
                      wandio_printf(f,"%s\n", buffer_str);
                    }
                }
              /* otherwise remove it from the map */
              else
                {
                  kh_del(bwv_v4pfx_timestamp, state->v4pfx_ts, k);
                }
            }
        }
      
      wandio_wdestroy(f);

      /* update next output time */
      state->next_output_time = state->next_output_time + state->out_interval;
    }


  /* compute processed delay */
  state->processed_delay = zclock_time()/1000 - bgpview_get_time(view);
  state->processing_time = STATE->processed_delay - STATE->arrival_delay;

  /* dump timeseries metrics */
  timeseries_kp_set(state->kp, state->arrival_delay_idx,
                    state->arrival_delay);

  timeseries_kp_set(state->kp, state->processed_delay_idx,
                    state->processed_delay);

  timeseries_kp_set(state->kp, state->processing_time_idx,
                    state->processing_time);

  timeseries_kp_set(state->kp, state->ipv4_visible_pfxs_count_idx,
                    kh_size(state->v4pfx_ts));

  if(timeseries_kp_flush(STATE->kp, bgpview_get_time(view)) != 0)
    {
      return -1;
    }

  return 0;
}
