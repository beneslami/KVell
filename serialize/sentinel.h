#ifndef SENTINEL_H
#define SENTINEL_H

#define SENTINEL_INSERTION_CODE(obj, b)                           \
{                                                                 \
    unsigned int sentinel = 0xFFFFFFFF;                           \
    if(!obj){                                                     \
      serialize_data(b, (char*)&sentinel, sizeof(unsigned int));  \
      return;                                                     \
    }                                                             \
}

#define SENTINEL_DETECTION_CODE(b)                                \
{                                                                 \
  unsigned int sentinel = 0;                                      \
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));   \
  if(sentinel == 0xFFFFFFFF)  return NULL;                        \
  serialize_buffer_skip(b, -1 * sizeof(unsigned int));            \
}

#endif
