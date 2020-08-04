#ifndef SERIALIZE_H
#define SERIALIZE_H

typedef struct ser_buff_{
  #define SERIALIZE_BUFFER_DEFAULT_SIZE 512
  void *b;
  int size;
  int next;
}ser_buff_t;

void init_serialized_buffer(ser_buff_t **b);
void init_serialized_buffer_of_defined_size(ser_buff_t **b, int size);
int is_serialized_buffer_empty(ser_buff_t *b);
int get_serialize_buffer_size(ser_buff_t *b);
int get_serialize_buffer_length(ser_buff_t *b);
int get_serialize_buffer_current_ptr_offset(ser_buff_t *b);
char *get_serialize_buffer_current_ptr(ser_buff_t *b);
void serialize_buffer_skip(ser_buff_t *b, int size);
void copy_in_serialized_buffer_by_offset(ser_buff_t *b, int size, char *value, int offset);
void serialize_data(ser_buff_t *b, char *data, int nbytes);
void de_serialize_data(char *dest, ser_buff_t *b, int size);
void free_serialize_buffer(ser_buff_t *b);
void truncate_serialize_buffer(ser_buff_t **b);
void reset_serialize_buffer(ser_buff_t *b);
void print_buffer_details(ser_buff_t *b);

#endif
