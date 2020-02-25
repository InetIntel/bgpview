/*
 * This file is part of bgpstream
 *
 * CAIDA, UC San Diego
 * bgpstream-info@caida.org
 *
 * Copyright (C) 2012 The Regents of the University of California.
 * Authors: Alistair King, Chiara Orsini, Ken Keys
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
#ifndef __BGPCORSARO_INT_H
#define __BGPCORSARO_INT_H

#include "bgpcorsaro.h"
#include "bgpstream.h"
#include "bgpview.h"
#include "config.h"

/** @file
 *
 * @brief Header file dealing with internal bgpcorsaro functions
 *
 * @author Alistair King
 *
 */


/* GCC optimizations */
/** @todo either make use of those that libtrace defines, or copy the way that
    libtrace does this*/
#if __GNUC__ >= 3
#ifndef DEPRECATED
#define DEPRECATED __attribute__((deprecated))
#endif
#ifndef SIMPLE_FUNCTION
#define SIMPLE_FUNCTION __attribute__((pure))
#endif
#ifndef UNUSED
#define UNUSED __attribute__((unused))
#endif
#ifndef PACKED
#define PACKED __attribute__((packed))
#endif
#ifndef PRINTF
#define PRINTF(formatpos, argpos)                                              \
  __attribute__((format(printf, formatpos, argpos)))
#endif
#else
#ifndef DEPRECATED
#define DEPRECATED
#endif
#ifndef SIMPLE_FUNCTION
#define SIMPLE_FUNCTION
#endif
#ifndef UNUSED
#define UNUSED
#endif
#ifndef PACKED
#define PACKED
#endif
#ifndef PRINTF
#define PRINTF(formatpos, argpos)
#endif
#endif

/**
 * @name Bgpcorsaro data structures
 *
 * These data structures are used when reading bgpcorsaro files with
 * libbgpcorsaro
 *
 * @{ */

/** Structure representing the start or end of an interval
 *
 * The start time represents the first second which this interval covers.
 * I.e. start.time <= pkt.time for all pkt in the interval
 * The end time represents the last second which this interval covers.
 * I.e. end.time >= pkt.time for all pkt in the interval
 *
 * If looking at the start and end interval records for a given interval,
 * the interval duration will be:
 * @code end.time - start.time + 1 @endcode
 * The +1 includes the final second in the time.
 *
 * If bgpcorsaro is shutdown at any time other than an interval boundary, the
 * end.time value will be the seconds component of the arrival time of the
 * last observed record.
 *
 * Values are all in HOST byte order
 */
struct bgpcorsaro_interval {
  /** The interval number (starts at 0) */
  uint16_t number;
  /** The time this interval started/ended */
  uint32_t time;
};

/** @} */

/** The interval after which we will end an interval */
#define BGPCORSARO_INTERVAL_DEFAULT 60

/** Bgpcorsaro output state */
struct bgpcorsaro {
  /** The local wall time that bgpcorsaro was started at */
  struct timeval init_time;

  /** The bgpstream pointer for the stream that we are being fed from */
  bgpstream_t *stream;

  /** The name of the monitor that bgpcorsaro is running on */
  char *monitorname;

  /** The template used to create bgpcorsaro output files */
  char *template;

  /** The compression type (based on the file name) */
  int compress;

  /** The compression level (ignored if not compressing) */
  int compress_level;

  /** The file to write log output to */
  iow_t *logfile;

  /** Has the user asked us not to log to a file? */
  int logfile_disabled;

  /** A borrowed pointer to a libtimeseries instance */
  timeseries_t *timeseries;

  /** A pointer to the record passed to the plugins */
  bgpstream_record_t *bsrecord;

  /** The first interval end will be rounded down to the nearest integer
      multiple of the interval length if enabled */
  int align_intervals;

  /** The number of seconds after which plugins will be asked to dump data */
  int interval;

  /** The output files will be rotated after n intervals if >0 */
  int output_rotate;

  /** The meta output files will be rotated after n intervals if >=0
   * a value of 0 indicates no rotation, <0 indicates the output_rotate
   * value should be used
   */
  int meta_output_rotate;

  /** State for the current interval */
  bgpcorsaro_interval_t interval_start;

  /** The time that this interval will be dumped at */
  long next_report;

  /** The time of the the first record seen by bgpcorsaro */
  long first_ts;

  /** The time of the most recent record seen by bgpcorsaro */
  long last_ts;

  /** Whether there are un-dumped records in the current interval */
  int interval_end_needed;

  /** The total number of records that have been processed */
  uint64_t record_cnt;

  /** Has this bgpcorsaro object been started yet? */
  int started;

  /** Has this bgpcorsaro reached EOF? */
  int eof;

  /** Minimum record time allowed */
  uint32_t minimum_time;

  /** Maximum allowed packet inter-arrival time */
  int gap_limit;

  /** Shared bgpview */
  bgpview_t *shared_view;
};

#ifdef WITH_PLUGIN_TIMING
/* Helper macros for doing timing */

/** Start a timer with the given name */
#define TIMER_START(timer)                                                     \
  struct timeval timer_start;                                                  \
  do {                                                                         \
    gettimeofday(&timer_start, NULL);                                          \
  } while (0)

#define TIMER_END(timer)                                                       \
  struct timeval timer_end, timer_diff;                                        \
  do {                                                                         \
    gettimeofday(&timer_end, NULL);                                            \
    timeval_subtract(&timer_diff, &timer_end, &timer_start);                   \
  } while (0)

#define TIMER_VAL(timer) ((timer_diff.tv_sec * 1000000) + timer_diff.tv_usec)
#endif

#endif /* __BGPCORSARO_INT_H */
