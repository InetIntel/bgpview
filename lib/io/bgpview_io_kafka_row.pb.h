/* Generated by the protocol buffer compiler.  DO NOT EDIT! */
/* Generated from: bgpview_io_kafka_row.proto */

#ifndef PROTOBUF_C_bgpview_5fio_5fkafka_5frow_2eproto__INCLUDED
#define PROTOBUF_C_bgpview_5fio_5fkafka_5frow_2eproto__INCLUDED

#include <protobuf-c/protobuf-c.h>

PROTOBUF_C__BEGIN_DECLS

#if PROTOBUF_C_VERSION_NUMBER < 1000000
# error This file was generated by a newer version of protoc-c which is incompatible with your libprotobuf-c headers. Please update your headers.
#elif 1001001 < PROTOBUF_C_MIN_COMPILER_VERSION
# error This file was generated by an older version of protoc-c which is incompatible with your libprotobuf-c headers. Please regenerate this file with a newer version of protoc-c.
#endif


typedef struct _BGPCell BGPCell;
typedef struct _BGPRow BGPRow;


/* --- enums --- */


/* --- messages --- */

struct  _BGPCell
{
  ProtobufCMessage base;
  int32_t peerid;
  ProtobufCBinaryData aspath;
};
#define BGPCELL__INIT \
 { PROTOBUF_C_MESSAGE_INIT (&bgpcell__descriptor) \
    , 0, {0,NULL} }


struct  _BGPRow
{
  ProtobufCMessage base;
  ProtobufCBinaryData pfx;
  size_t n_cells;
  BGPCell **cells;
  char *operation;
};
#define BGPROW__INIT \
 { PROTOBUF_C_MESSAGE_INIT (&bgprow__descriptor) \
    , {0,NULL}, 0,NULL, NULL }


/* BGPCell methods */
void   bgpcell__init
                     (BGPCell         *message);
size_t bgpcell__get_packed_size
                     (const BGPCell   *message);
size_t bgpcell__pack
                     (const BGPCell   *message,
                      uint8_t             *out);
size_t bgpcell__pack_to_buffer
                     (const BGPCell   *message,
                      ProtobufCBuffer     *buffer);
BGPCell *
       bgpcell__unpack
                     (ProtobufCAllocator  *allocator,
                      size_t               len,
                      const uint8_t       *data);
void   bgpcell__free_unpacked
                     (BGPCell *message,
                      ProtobufCAllocator *allocator);
/* BGPRow methods */
void   bgprow__init
                     (BGPRow         *message);
size_t bgprow__get_packed_size
                     (const BGPRow   *message);
size_t bgprow__pack
                     (const BGPRow   *message,
                      uint8_t             *out);
size_t bgprow__pack_to_buffer
                     (const BGPRow   *message,
                      ProtobufCBuffer     *buffer);
BGPRow *
       bgprow__unpack
                     (ProtobufCAllocator  *allocator,
                      size_t               len,
                      const uint8_t       *data);
void   bgprow__free_unpacked
                     (BGPRow *message,
                      ProtobufCAllocator *allocator);
/* --- per-message closures --- */

typedef void (*BGPCell_Closure)
                 (const BGPCell *message,
                  void *closure_data);
typedef void (*BGPRow_Closure)
                 (const BGPRow *message,
                  void *closure_data);

/* --- services --- */


/* --- descriptors --- */

extern const ProtobufCMessageDescriptor bgpcell__descriptor;
extern const ProtobufCMessageDescriptor bgprow__descriptor;

PROTOBUF_C__END_DECLS


#endif  /* PROTOBUF_C_bgpview_5fio_5fkafka_5frow_2eproto__INCLUDED */
