/*
 * This file is part of bgpstream
 *
 * CAIDA, UC San Diego
 * bgpstream-info@caida.org
 *
 * Copyright (C) 2012 The Regents of the University of California.
 * Authors: Danilo Giordano, Alistair King, Chiara Orsini
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

#include "bgpview.h"
#include "bgpview_io_kafka_int.h"
#include "config.h"
#include "utils.h"
#include <assert.h>
#include <errno.h>
#include <librdkafka/rdkafka.h>
#include <string.h>
#ifdef HAVE_TIME_H
#include <time.h>
#endif
#ifdef HAVE_SYS_TIME_H
#include <sys/time.h>
#endif

#define BUFFER_LEN 16384

#define STAT(name) (client->stats.name)

#define SEND_MSG(topic_id, partition, buf, len)                         \
  do {                                                                  \
    if (rd_kafka_produce(RKT(topic_id), (partition),                    \
                         RD_KAFKA_MSG_F_COPY, (buf), (len),             \
                         NULL, 0, NULL) == -1) {                        \
      fprintf(stderr,                                                   \
              "ERROR: Failed to produce to topic %s partition %i: %s\n", \
              rd_kafka_topic_name(RKT(topic_id)),                       \
              (partition),                                              \
              rd_kafka_err2str(rd_kafka_errno2err(errno)));             \
      rd_kafka_poll(client->rdk_conn, 0);                               \
      goto err;                                                         \
    }                                                                   \
  } while (0)

#define RESET_BUF(buf, ptr, written)            \
  do {                                          \
    (ptr) = (buf); (written) = 0;               \
  } while (0)

static int64_t get_offset(bgpview_io_kafka_t *client, char *topic,
                          int32_t partition)
{
  int64_t low = 0;
  int64_t high = 0;

  if (rd_kafka_query_watermark_offsets(client->rdk_conn, topic, partition, &low,
                                       &high,
                                       10000) == RD_KAFKA_RESP_ERR_NO_ERROR) {
    return high;
  }

  return -1;
}

static int pfx_row_serialize(uint8_t *buf, size_t len, char operation,
                             bgpview_iter_t *it, bgpview_io_filter_cb_t *cb)
{
  size_t written = 0;
  ssize_t s;

  // serialize the operation that must be done with this row
  // "Update" or "Remove"
  BGPVIEW_IO_SERIALIZE_VAL(buf, len, written, operation);
  if ((s = bgpview_io_serialize_pfx_row(buf, (len - written), it, cb,
                                        operation == 'R' ? -1 : 0)) == -1) {
    goto err;
  }
  written += s;
  buf += s;

  return written;

err:
  return -1;
}

static int pfx_row_start(uint8_t *buf, size_t len, char operation,
                         bgpstream_pfx_t *pfx)
{
  size_t written = 0;
  ssize_t s;

  // serialize the operation that must be done with this row
  // "Update" or "Remove"
  BGPVIEW_IO_SERIALIZE_VAL(buf, len, written, operation);

  // send the prefix
  if ((s = bgpview_io_serialize_pfx(buf, (len - written), pfx))
      == -1) {
    goto err;
  }
  written += s;
  buf += s;

  return written;

 err:
  return -1;
}

static int pfx_row_end(uint8_t *buf, size_t len, uint16_t peer_cnt)
{
  size_t written = 0;
  uint16_t u16;

  /* send a magic peerid to indicate end of peers */
  u16 = BGPVIEW_IO_END_OF_PEERS;
  BGPVIEW_IO_SERIALIZE_VAL(buf, len, written, u16);

  /* peer cnt for cross validation */
  u16 = htons(peer_cnt);
  BGPVIEW_IO_SERIALIZE_VAL(buf, len, written, u16);

  return written;
}

/* returns 0 if they are the same */
static int diff_cells(bgpview_iter_t *parent_view_it, bgpview_iter_t *itC)
{
  bgpstream_as_path_store_path_id_t idxH =
    bgpview_iter_pfx_peer_get_as_path_store_path_id(parent_view_it);
  bgpstream_as_path_store_path_id_t idxC =
    bgpview_iter_pfx_peer_get_as_path_store_path_id(itC);

  return bcmp(&idxH, &idxC, sizeof(bgpstream_as_path_store_path_id_t)) != 0;
}

#if 0
/* returns 0 if they are the same */
static int diff_rows(bgpview_iter_t *parent_view_it, bgpview_iter_t *itC)
{
  int npeersH =
    bgpview_iter_pfx_get_peer_cnt(parent_view_it, BGPVIEW_FIELD_ACTIVE);
  int npeersC = bgpview_iter_pfx_get_peer_cnt(itC, BGPVIEW_FIELD_ACTIVE);

  if (npeersH != npeersC)
    return 1;

  bgpstream_pfx_t *pfx = bgpview_iter_pfx_get_pfx(itC);
  bgpstream_peer_id_t peerid;

  for (bgpview_iter_pfx_first_peer(itC, BGPVIEW_FIELD_ACTIVE);
       bgpview_iter_pfx_has_more_peer(itC); bgpview_iter_pfx_next_peer(itC)) {
    peerid = bgpview_iter_peer_get_peer_id(itC);
    if (bgpview_iter_seek_pfx_peer(parent_view_it, pfx, peerid,
                                   BGPVIEW_FIELD_ACTIVE,
                                   BGPVIEW_FIELD_ACTIVE) == 0 ||
        diff_paths(parent_view_it, itC) != 0) {
      return 1;
    }
  }
  return 0;
}
#endif

/* ==========END SUPPORT FUNCTIONS ========== */

/* ==========START SEND/RECEIVE FUNCTIONS ========== */

int bgpview_io_kafka_producer_send_members_update(bgpview_io_kafka_t *client,
                                                  uint32_t time_now)
{
  uint8_t buf[BUFFER_LEN];
  uint8_t *ptr = buf;
  size_t len = BUFFER_LEN;
  size_t written = 0;

  fprintf(stderr, "INFO: Sending update to members topic at %d\n", time_now);

  /* Identity */
  uint16_t ident_len = strlen(client->identity);
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, ident_len);
  assert((len-written) >= ident_len);
  memcpy(ptr, client->identity, ident_len);
  ptr += ident_len;
  written += ident_len;

  /* Wall time (or 0 in the case that we are shutting down) */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, time_now);

  SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_MEMBERS,
           BGPVIEW_IO_KAFKA_MEMBERS_PARTITION_DEFAULT,
           buf, written);

  client->prod_state.next_members_update =
    time_now + BGPVIEW_IO_KAFKA_MEMBERS_UPDATE_INTERVAL_DEFAULT;

  /* Wait for messages to be delivered */
  while (rd_kafka_outq_len(client->rdk_conn) > 0) {
    rd_kafka_poll(client->rdk_conn, 100);
  }

  return 0;

 err:
  return -1;
}

static int send_metadata(bgpview_io_kafka_t *client,
                         bgpview_io_kafka_md_t *meta)
{
  uint8_t buf[BUFFER_LEN];
  uint8_t *ptr = buf;
  size_t len = BUFFER_LEN;
  size_t written = 0;

  /* Serialize the common metadata header */

  /* Identity */
  uint16_t ident_len = strlen(client->identity);
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, ident_len);
  assert((len-written) >= ident_len);
  memcpy(ptr, client->identity, ident_len);
  ptr += ident_len;
  written += ident_len;

  /* Time */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, meta->time);

  /* Prefixes offset */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, meta->pfxs_offset);

  /* Peers offset (no partitions for peers) */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, meta->peers_offset);

  /* Serialize the dump type ('S' -> Sync, or 'D' -> Diff) */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, meta->type);

  /* now serialize info specific to to the dump type */
  switch (meta->type) {
  case 'S':
    /* nothing additional */
    break;

  case 'D':
    /** Offset of most recent sync frame */
    BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, meta->sync_md_offset);

    /** Time of the parent view */
    BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, meta->parent_time);
    break;

  default:
    goto err;
  }

  SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_META,
           BGPVIEW_IO_KAFKA_METADATA_PARTITION_DEFAULT,
           buf, written);

  /* Wait for messages to be delivered */
  while (rd_kafka_outq_len(client->rdk_conn) > 0) {
    rd_kafka_poll(client->rdk_conn, 100);
  }

  return 0;

err:
  return -1;
}

static int send_peers(bgpview_io_kafka_t *client,
                      bgpview_io_kafka_md_t *meta,
                      bgpview_t *view,
                      bgpview_iter_t *it,
                      bgpview_iter_t *parent_view_it,
                      bgpview_io_filter_cb_t *cb)
{
  uint8_t buf[BUFFER_LEN];
  uint8_t *ptr = buf;
  size_t len = BUFFER_LEN;
  ssize_t written = 0;

  char type;

  uint16_t peers_tx = 0;
  int filter;

  /* find our current offset and update the metadata */
  if ((meta->peers_offset =
         get_offset(client, TNAME(BGPVIEW_IO_KAFKA_TOPIC_ID_PEERS),
                    BGPVIEW_IO_KAFKA_PEERS_PARTITION_DEFAULT)) < 0) {
    fprintf(stderr, "ERROR: Could not get peer offset\n");
    goto err;
  }

  for (bgpview_iter_first_peer(it, BGPVIEW_FIELD_ACTIVE);
       bgpview_iter_has_more_peer(it); bgpview_iter_next_peer(it)) {
    /* if we are sending a diff, only send if this peer is not in our
       reference diff */
    if (meta->type == 'D' &&
        bgpview_iter_seek_peer(parent_view_it,
                               bgpview_iter_peer_get_peer_id(it),
                               BGPVIEW_FIELD_ACTIVE) == 1) {
      continue;
    }

    if (cb != NULL) {
      /* ask the caller if they want this peer */
      if ((filter = cb(it, BGPVIEW_IO_FILTER_PEER)) < 0) {
        goto err;
      }
      if (filter == 0) {
        continue;
      }
    }
    /* past here means this peer is being sent */
    peers_tx++;

    type = 'P';
    BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, type);

    if ((written = bgpview_io_serialize_peer(
           ptr, (len - written), bgpview_iter_peer_get_peer_id(it),
           bgpview_iter_peer_get_sig(it))) < 0) {
      goto err;
    }

    SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_PEERS,
             BGPVIEW_IO_KAFKA_PEERS_PARTITION_DEFAULT,
             buf, written);
    RESET_BUF(buf, ptr, written);
  }

  /* End message */
  type = 'E';
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, type);
  /* View time */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, meta->time);
  /* Peer Count */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, peers_tx);

  SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_PEERS,
           BGPVIEW_IO_KAFKA_PEERS_PARTITION_DEFAULT,
           buf, written);

  while (rd_kafka_outq_len(client->rdk_conn) > 0) {
    rd_kafka_poll(client->rdk_conn, 100);
  }

  return 0;

err:
  return -1;
}

static int send_pfxs(bgpview_io_kafka_t *client,
                     bgpview_io_kafka_md_t *meta,
                     bgpview_iter_t *it,
                     bgpview_t *parent_view,
                     bgpview_iter_t *parent_view_it,
                     bgpview_io_filter_cb_t *cb)
{
  int filter;

  uint8_t buf[BUFFER_LEN];
  uint8_t *ptr = buf;
  size_t len = BUFFER_LEN;
  size_t written = 0;
  ssize_t s = 0;

  bgpview_t *view = bgpview_iter_get_view(it);
  assert(view != NULL);
  bgpstream_pfx_t *pfx;
  bgpstream_peer_id_t peerid;

  int send_cell;
  int cell_cnt;
  int common_cells;
  uint32_t pfxs_tx = 0;
  uint32_t cells_tx = 0;

  int pfxs_cnt_ref = 0;
  int pfxs_cnt_cur = 0;

  /* find our current offset and update the metadata */
  if ((meta->pfxs_offset =
       get_offset(client, TNAME(BGPVIEW_IO_KAFKA_TOPIC_ID_PFXS),
                    BGPVIEW_IO_KAFKA_PFXS_PARTITION_DEFAULT)) < 0) {
    fprintf(stderr, "ERROR: Could not get prefix offset\n");
    goto err;
  }

  if (meta->type == 'D') {
    pfxs_cnt_ref = bgpview_pfx_cnt(parent_view, BGPVIEW_FIELD_ACTIVE);
    pfxs_cnt_cur = bgpview_pfx_cnt(view, BGPVIEW_FIELD_ACTIVE);
  }

  for (bgpview_iter_first_pfx(it, 0, BGPVIEW_FIELD_ACTIVE);
       bgpview_iter_has_more_pfx(it); bgpview_iter_next_pfx(it)) {
    /* reset the buffer */
    written = 0;
    ptr = buf;

    if (cb != NULL) {
      if ((filter = cb(it, BGPVIEW_IO_FILTER_PFX)) < 0) {
        goto err;
      }
      if (filter == 0) {
        continue;
      }
    }

    if (meta->type == 'D') {
      pfx = bgpview_iter_pfx_get_pfx(it);
      if (bgpview_iter_seek_pfx(parent_view_it, pfx,
                                BGPVIEW_FIELD_ACTIVE) == 1) {
        STAT(common_pfxs_cnt)++;
        cell_cnt = 0;
        common_cells = 0;
        // for each pfx-peer in this row, see if it has changed
        for (bgpview_iter_pfx_first_peer(it, BGPVIEW_FIELD_ACTIVE);
             bgpview_iter_pfx_has_more_peer(it);
             bgpview_iter_pfx_next_peer(it))
          {
            peerid = bgpview_iter_peer_get_peer_id(it);
            send_cell = 0;
            // does this pfx-peer exist in the parent view?
            if (bgpview_iter_pfx_seek_peer(parent_view_it, peerid,
                                           BGPVIEW_FIELD_ACTIVE) == 1) {
              // ok, it exists, but has it changed?
              if (diff_cells(parent_view_it, it) != 0) {
                // cell has changed wrt parent
                send_cell = 1;
                STAT(changed_pfx_peer_cnt)++;
              }
              common_cells++;
            } else {
              // doesn't exist in the parent, send it
              STAT(added_pfx_peer_cnt)++;
              send_cell = 1;
            }

            if (send_cell != 0) {
              // is this the first cell?
              if (cell_cnt == 0) {
                if ((s = pfx_row_start(ptr, (len - written), 'U',
                                       bgpview_iter_pfx_get_pfx(it)))
                    == -1) {
                  goto err;
                }
                written += s;
                ptr += s;
                pfxs_tx++;
              }
              // send the cell
              if ((s =
                   bgpview_io_serialize_pfx_peer(ptr, (len - written), it, 0))
                  == -1) {
                goto err;
              }
              written += s;
              ptr += s;
              cell_cnt++;
              cells_tx++;
            }
          }
        // if there were cells, we sent something, end the row
        if (cell_cnt > 0) {
          STAT(changed_pfxs_cnt)++;
          if ((s = pfx_row_end(ptr, (len - written), cell_cnt)) == -1) {
            goto err;
          }
          written += s;
          ptr += s;
          SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_PFXS,
                   BGPVIEW_IO_KAFKA_PFXS_PARTITION_DEFAULT,
                   buf, written);
          RESET_BUF(buf, ptr, written);
        }

        // Chiara's optimization:
        int ppc = bgpview_iter_pfx_get_peer_cnt(parent_view_it,
                                                BGPVIEW_FIELD_ACTIVE);
        int cpc =  bgpview_iter_pfx_get_peer_cnt(it, BGPVIEW_FIELD_ACTIVE);
        if (!(ppc == cpc && cpc == common_cells)) {
          // there may have been deleted cells
          // for each pfx-peer in the old row, see if it has disappeared
          cell_cnt = 0;
          for (bgpview_iter_pfx_first_peer(parent_view_it, BGPVIEW_FIELD_ACTIVE);
               bgpview_iter_pfx_has_more_peer(parent_view_it);
               bgpview_iter_pfx_next_peer(parent_view_it))
            {
              peerid = bgpview_iter_peer_get_peer_id(parent_view_it);
              if (bgpview_iter_pfx_seek_peer(it, peerid,
                                             BGPVIEW_FIELD_ACTIVE) != 1) {
                // remove this cell
                STAT(removed_pfx_peer_cnt)++;
                if (cell_cnt == 0) {
                  // send the pfx info now
                  if ((s =
                       pfx_row_start(ptr, (len - written), 'R',
                                     bgpview_iter_pfx_get_pfx(parent_view_it)))
                      == -1) {
                    goto err;
                  }
                  written += s;
                  ptr += s;
                  pfxs_tx++;
                }
                if ((s =
                     bgpview_io_serialize_pfx_peer(ptr, (len - written),
                                                   parent_view_it, -1))
                    == -1) {
                  goto err;
                }
                written += s;
                ptr += s;
                cell_cnt++;
                cells_tx++;
              }
            }
          // if we removed any cells, need to end the row
          if (cell_cnt > 0) {
            if ((s = pfx_row_end(ptr, (len - written), cell_cnt)) == -1) {
              goto err;
            }
            written += s;
            ptr += s;
            SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_PFXS,
                     BGPVIEW_IO_KAFKA_PFXS_PARTITION_DEFAULT,
                     buf, written);
            RESET_BUF(buf, ptr, written);
          }
        }
      } else {
        // send the full row
        STAT(added_pfxs_cnt)++;
        if ((s = pfx_row_serialize(ptr, len, 'U', it, cb)) < 0) {
          goto err;
        }
        written += s;
        ptr += s;
        pfxs_tx++;
        cells_tx += bgpview_iter_pfx_get_peer_cnt(it, BGPVIEW_FIELD_ACTIVE);
        SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_PFXS,
                 BGPVIEW_IO_KAFKA_PFXS_PARTITION_DEFAULT,
                 buf, written);
        RESET_BUF(buf, ptr, written);
      }
    } else { // SYNC view, send the full row
      if ((s = pfx_row_serialize(ptr, len, 'U', it, cb)) < 0) {
        goto err;
      }
      written += s;
      ptr += s;
      pfxs_tx++;
      cells_tx += bgpview_iter_pfx_get_peer_cnt(it, BGPVIEW_FIELD_ACTIVE);
      SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_PFXS,
               BGPVIEW_IO_KAFKA_PFXS_PARTITION_DEFAULT,
               buf, written);
      RESET_BUF(buf, ptr, written);
    }
  }
  rd_kafka_poll(client->rdk_conn, 0);

  if (meta->type == 'D') {
    /* send removals */
    STAT(removed_pfxs_cnt) = pfxs_cnt_ref - STAT(common_pfxs_cnt);
    assert(STAT(removed_pfxs_cnt) >= 0);

    STAT(added_pfxs_cnt) =
      (pfxs_cnt_cur - STAT(common_pfxs_cnt)) + STAT(removed_pfxs_cnt);
    if (STAT(added_pfxs_cnt) < 0) {
      STAT(added_pfxs_cnt) = 0;
    }

    STAT(pfx_cnt) = STAT(common_pfxs_cnt) + STAT(added_pfxs_cnt);
    STAT(sync_pfx_cnt) = 0;

    if (STAT(removed_pfxs_cnt) > 0) {
      int remain = STAT(removed_pfxs_cnt);
      for (bgpview_iter_first_pfx(parent_view_it, 0,
                                  BGPVIEW_FIELD_ACTIVE);
           bgpview_iter_has_more_pfx(parent_view_it);
           bgpview_iter_next_pfx(parent_view_it)) {
        written = 0;
        ptr = buf;

        pfx = bgpview_iter_pfx_get_pfx(parent_view_it);

        if (bgpview_iter_seek_pfx(it, pfx, BGPVIEW_FIELD_ACTIVE) != 0) {
          continue;
        }

        if ((s = pfx_row_serialize(ptr, (len - written), 'R',
                                   parent_view_it, cb)) < 0) {
          goto err;
        }
        written += s;
        ptr += s;

        remain--;
        pfxs_tx++;
        SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_PFXS,
                 BGPVIEW_IO_KAFKA_PFXS_PARTITION_DEFAULT,
                 buf, written);
        RESET_BUF(buf, ptr, written);

        /* stop looking if we have removed all we need to */
        if (remain == 0) {
          break;
        }
      }
    }
  } else {
    // update sync-only stats
    STAT(pfx_cnt) = STAT(sync_pfx_cnt) =
      bgpview_pfx_cnt(view, BGPVIEW_FIELD_ACTIVE);
  }

  /* send the end message */
  written = 0;
  ptr = buf;
  char type = 'E';
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, type);
  /* Time */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, meta->time);
  /* Prefix count */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, pfxs_tx);
  /* Cell count */
  BGPVIEW_IO_SERIALIZE_VAL(ptr, len, written, cells_tx);

  SEND_MSG(BGPVIEW_IO_KAFKA_TOPIC_ID_PFXS,
           BGPVIEW_IO_KAFKA_PFXS_PARTITION_DEFAULT,
           buf, written);
  RESET_BUF(buf, ptr, written);

  return 0;

err:
  return -1;
}

static int send_sync_view(bgpview_io_kafka_t *client,
                          bgpview_t *view,
                          bgpview_io_filter_cb_t *cb)
{
  bgpview_iter_t *it = NULL;
  bgpview_io_kafka_md_t meta;

  if ((it = bgpview_iter_create(view)) == NULL) {
    goto err;
  }

  meta.time = bgpview_get_time(view);
  meta.type = 'S';

  if (send_peers(client, &meta, view, it, NULL, cb) != 0) {
    goto err;
  }
  if (send_pfxs(client, &meta, it, NULL, NULL, cb) != 0) {
    goto err;
  }

  /* find the current metadata offset and update the sync info */
  if ((client->prod_state.last_sync_offset =
       get_offset(client, TNAME(BGPVIEW_IO_KAFKA_TOPIC_ID_META),
                    BGPVIEW_IO_KAFKA_METADATA_PARTITION_DEFAULT)) < 0) {
    fprintf(stderr, "ERROR: Could not get metadata offset\n");
    goto err;
  }

  if (send_metadata(client, &meta) == -1) {
    fprintf(stderr, "Error publishing metadata\n");
    goto err;
  }

  bgpview_iter_destroy(it);

  return 0;

err:
  return -1;
}

static int send_diff_view(bgpview_io_kafka_t *client,
                          bgpview_t *view,
                          bgpview_t *parent_view,
                          bgpview_io_filter_cb_t *cb)
{
  bgpview_iter_t *it = NULL;
  bgpview_iter_t *parent_view_it = NULL;
  bgpview_io_kafka_md_t meta;

  if ((it = bgpview_iter_create(view)) == NULL) {
    goto err;
  }

  if ((parent_view_it = bgpview_iter_create(parent_view)) == NULL) {
    goto err;
  }

  meta.time = bgpview_get_time(view);
  meta.type = 'D';

  assert(parent_view != NULL && bgpview_get_time(parent_view) != 0);
  meta.parent_time = bgpview_get_time(parent_view);
  meta.sync_md_offset = client->prod_state.last_sync_offset;

  if (send_peers(client, &meta, view, it, parent_view_it, cb) == -1) {
    goto err;
  }

  if (send_pfxs(client, &meta, it, parent_view, parent_view_it, cb) == -1) {
    goto err;
  }

  if (send_metadata(client, &meta) == -1) {
    fprintf(stderr, "Error on publishing the offset\n");
    goto err;
  }

  bgpview_iter_destroy(it);
  bgpview_iter_destroy(parent_view_it);

  return 0;

err:
  bgpview_iter_destroy(it);
  bgpview_iter_destroy(parent_view_it);
  return -1;
}

/* ==========END SEND/RECEIVE FUNCTIONS ========== */

/* ========== PROTECTED FUNCTIONS ========== */

int bgpview_io_kafka_producer_connect(bgpview_io_kafka_t *client)
{
  rd_kafka_conf_t *conf = rd_kafka_conf_new();
  char errstr[512];

  if (bgpview_io_kafka_common_config(client, conf) != 0) {
    goto err;
  }

  if (rd_kafka_conf_set(conf, "compression.codec", "snappy", errstr,
                        sizeof(errstr)) != RD_KAFKA_CONF_OK) {
    fprintf(stderr, "ERROR: %s\n", errstr);
    goto err;
  }

  // Disable logging of connection close/idle timeouts caused by Kafka 0.9.x
  //   See https://github.com/edenhill/librdkafka/issues/437 for more details.
  // TODO: change this when librdkafka has better handling of idle disconnects
  if (rd_kafka_conf_set(conf, "log.connection.close", "false", errstr,
                        sizeof(errstr)) != RD_KAFKA_CONF_OK) {
    fprintf(stderr, "ERROR: %s\n", errstr);
    goto err;
  }

  // Since our prefix table is a flood of messages, batch them up
  if (rd_kafka_conf_set(conf, "batch.num.messages", "10000", errstr,
                        sizeof(errstr)) != RD_KAFKA_CONF_OK) {
    fprintf(stderr, "ERROR: %s\n", errstr);
    goto err;
  }
  // But don't wait very long before sending a partial batch (0.5s)
  if (rd_kafka_conf_set(conf, "queue.buffering.max.ms", "500", errstr,
                        sizeof(errstr)) != RD_KAFKA_CONF_OK) {
    fprintf(stderr, "ERROR: %s\n", errstr);
    goto err;
  }
  // And allow the queue to hold a full pfx table
  if (rd_kafka_conf_set(conf, "queue.buffering.max.messages", "7000000", errstr,
                        sizeof(errstr)) != RD_KAFKA_CONF_OK) {
    fprintf(stderr, "ERROR: %s\n", errstr);
    goto err;
  }

  if ((client->rdk_conn = rd_kafka_new(RD_KAFKA_PRODUCER, conf, errstr,
                                       sizeof(errstr))) == NULL) {
    fprintf(stderr, "ERROR: Failed to create new producer: %s\n", errstr);
    goto err;
  }

  if (rd_kafka_brokers_add(client->rdk_conn, client->brokers) == 0) {
    fprintf(stderr, "ERROR: No valid brokers specified\n");
    goto err;
  }

  client->connected = 1;

  // poll for errors
  rd_kafka_poll(client->rdk_conn, 5000);

  return client->fatal_error;

err:
  return -1;
}

int bgpview_io_kafka_producer_topic_connect(bgpview_io_kafka_t *client,
                                            rd_kafka_topic_t **rkt, char *topic)
{
  if ((*rkt = rd_kafka_topic_new(client->rdk_conn, topic, NULL)) == NULL) {
    return -1;
  }

  return 0;
}

int bgpview_io_kafka_producer_send(bgpview_io_kafka_t *client,
                                   bgpview_t *view,
                                   bgpview_t *parent_view,
                                   bgpview_io_filter_cb_t *cb)
{
  /* reset the stats */
  memset(&client->stats, 0, sizeof(bgpview_io_kafka_stats_t));

  // if it has been a while since we told the members topic about ourselves,
  // lets do that now
  struct timeval tv;
  gettimeofday(&tv, NULL);
  if (client->prod_state.next_members_update <= tv.tv_sec &&
      bgpview_io_kafka_producer_send_members_update(client, tv.tv_sec) != 0) {
    goto err;
  }

  if (parent_view == NULL) {
    if (send_sync_view(client, view, cb) != 0) {
      goto err;
    }
  } else {
    if (send_diff_view(client, view, parent_view, cb) != 0) {
      goto err;
    }
  }

  // wait for the queue to drain
  //while (rd_kafka_outq_len(client->rdk_conn) > 0) {
  rd_kafka_poll(client->rdk_conn, 100);
  //}

  return 0;

err:
  return -1;
}
