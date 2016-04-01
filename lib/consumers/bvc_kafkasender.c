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

#include "config.h"
#include "bvc_kafkasender.h"
#include "bgpview_io_kafka.h"
#include "utils.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <czmq.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <time.h>

#define NAME "kafka-sender"
#define CONSUMER_METRIC_PREFIX       "view.consumer.kafka-sender"

#define BUFFER_LEN 1024
#define META_METRIC_PREFIX_FORMAT  "%s."CONSUMER_METRIC_PREFIX".meta.%s"

/** A Sync frame will be sent once per N views */
#define SYNC_FREQUENCY 12

/* macro to access the current consumer state */
#define STATE					\
  (BVC_GET_STATE(consumer, kafkasender))

/* macro to access the current chain state, i.e.
 * the state variables shared by other consumers */
#define CHAIN_STATE                             \
  (BVC_GET_CHAIN_STATE(consumer))


/* our 'class' */
static bvc_t bvc_kafkasender = {
  BVC_ID_KAFKASENDER,
  NAME,
  BVC_GENERATE_PTRS(kafkasender)
};



/* our 'instance' */
typedef struct bvc_kafkasender_state {

  bgpview_io_kafka_t *client;

  /** Timeseries Key Package */
  timeseries_kp_t *kp;

  /** Sync frequency */
  int sync_freq;

  /** Number of diffs sent */
  int num_diffs;

  /** Parent view */
  bgpview_t *parent_view;

  int send_time_idx;
  int copy_time_idx;
  int proc_time_idx;
  int arr_delay_time_idx;

  int common_idx;
  int add_idx;
  int remove_idx;
  int change_idx;
  int pfx_cnt_idx;

  int sync_cnt_idx;

} bvc_kafkasender_state_t;

/** Create timeseries metrics */
static int create_ts_metrics(bvc_t *consumer)
{

  char buffer[BUFFER_LEN];
  bvc_kafkasender_state_t *state = STATE;

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "timing.send_time");
  if((state->send_time_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "timing.copy_time");
  if((state->copy_time_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "timing.processing_time");
  if((state->proc_time_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "timing.arrival_delay");
  if((state->arr_delay_time_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "diffs.common_pfx_cnt");
  if((state->common_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "diffs.added_pfx_cnt");
  if((state->add_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "diffs.removed_pfx_cnt");
  if((state->remove_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "diffs.changed_pfx_cnt");
  if((state->change_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "sync.pfx_cnt");
  if((state->sync_cnt_idx =
      timeseries_kp_add_key(STATE->kp, buffer)) == -1)
    {
      return -1;
    }

  snprintf(buffer, BUFFER_LEN, META_METRIC_PREFIX_FORMAT,
           CHAIN_STATE->metric_prefix, "pfx_cnt");
  if((state->pfx_cnt_idx =
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
	  "consumer usage: %s [options]\n"
          "       -k <kafka-brokers>    List of Kafka brokers (default: %s)\n"
          "       -s <sync-frequency>   Sync frame freq. in # views (default: %d)\n",
	  consumer->name,
          BGPVIEW_IO_KAFKA_BROKER_URI_DEFAULT,
          SYNC_FREQUENCY);
}

/** Parse the arguments given to the consumer */
static int parse_args(bvc_t *consumer, int argc, char **argv)
{
  int opt, prevoptind;

  assert(argc > 0 && argv != NULL);

  /* NB: remember to reset optind to 1 before using getopt! */
  optind = 1;

  /* remember the argv strings DO NOT belong to us */
  while(prevoptind = optind,
        (opt = getopt(argc, argv, ":k:s:?")) >= 0)
    {
      if (optind == prevoptind + 2 && optarg && *optarg == '-' ) {
        opt = ':';
        -- optind;
      }
      switch(opt)
	{
        case 'k':
          if(bgpview_io_kafka_set_broker_addresses(STATE->client,
                                                   optarg) != 0) {
            fprintf(stderr, "ERROR: Could not set broker addresses\n");
            return -1;
          }
          break;

        case 's':
          STATE->sync_freq = atoi(optarg);
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

bvc_t *bvc_kafkasender_alloc()
{
  return &bvc_kafkasender;
}


int bvc_kafkasender_init(bvc_t *consumer, int argc, char **argv)
{
  bvc_kafkasender_state_t *state = NULL;

  if((state = malloc_zero(sizeof(bvc_kafkasender_state_t))) == NULL)
    {
      return -1;
    }

  BVC_SET_STATE(consumer, state);

  state->client=bgpview_io_kafka_init(BGPVIEW_IO_KAFKA_MODE_PRODUCER);
  state->sync_freq = SYNC_FREQUENCY;

  /* parse the command line args */
  if(parse_args(consumer, argc, argv) != 0)
    {
      goto err;
    }

  if (bgpview_io_kafka_start(state->client) != 0) {
    fprintf(stderr, "ERROR: Could not start Kafka client\n");
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
  return -1;
}


void bvc_kafkasender_destroy(bvc_t *consumer)
{
  bvc_kafkasender_state_t *state = STATE;

  if(state == NULL)
    {
      return;
    }

  /* deallocate dynamic memory HERE */

  timeseries_kp_free(&state->kp);
  bgpview_io_kafka_destroy(state->client);
  state->client = NULL;

  bgpview_destroy(state->parent_view);
  state->parent_view = NULL;

  free(state);

  BVC_SET_STATE(consumer, NULL);
}


int bvc_kafkasender_process_view(bvc_t *consumer, bgpview_t *view)
{
  bvc_kafkasender_state_t *state = STATE;

  bgpview_t *pvp = NULL;

  uint64_t start_time = zclock_time()/1000;
  uint64_t arrival_delay = zclock_time()/1000 - bgpview_get_time(view);

  // are we sending a sync frame or a diff frame?
  if (state->parent_view == NULL || state->num_diffs == state->sync_freq-1) {
    state->num_diffs = 0;
    pvp = NULL;
  } else {
    pvp = state->parent_view;
    state->num_diffs++;
  }

  // send the view
  if (bgpview_io_kafka_send_view(state->client, view, pvp, NULL) != 0)
    {
      return -1;
    }

  uint64_t send_end = zclock_time()/1000;
  uint64_t send_time = send_end - start_time;

  // do the create/copy
  if ((state->parent_view == NULL &&
       (state->parent_view = bgpview_dup(view)) == NULL) ||
      bgpview_copy(state->parent_view, view) != 0) {
    fprintf(stderr, "ERROR: Could not copy view\n");
    return -1;
  }

  uint64_t copy_end = zclock_time()/1000;
  uint64_t copy_time = send_end - copy_end;
  uint64_t proc_time = copy_end - start_time;

  // set timeseries metrics
  bgpview_io_kafka_stats_t *stats = bgpview_io_kafka_get_stats(state->client);

  timeseries_kp_set(state->kp, state->send_time_idx, send_time);
  timeseries_kp_set(state->kp, state->copy_time_idx, copy_time);
  timeseries_kp_set(state->kp, state->proc_time_idx, proc_time);
  timeseries_kp_set(state->kp, state->arr_delay_time_idx, arrival_delay);

  timeseries_kp_set(state->kp, state->common_idx, stats->common_pfxs_cnt);
  timeseries_kp_set(state->kp, state->add_idx, stats->added_pfxs_cnt);
  timeseries_kp_set(state->kp, state->remove_idx, stats->removed_pfxs_cnt);
  timeseries_kp_set(state->kp, state->change_idx, stats->changed_pfxs_cnt);

  timeseries_kp_set(state->kp, state->pfx_cnt_idx, stats->pfx_cnt);

  timeseries_kp_set(state->kp, state->sync_cnt_idx, stats->sync_pfx_cnt);

  // flush
  if(timeseries_kp_flush(STATE->kp, bgpview_get_time(view)) != 0)
    {
      fprintf(stderr, "Warning: could not flush %s %"PRIu32"\n",
              NAME, bgpview_get_time(view));
    }

  return 0;
}
