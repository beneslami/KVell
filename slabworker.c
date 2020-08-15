#include "headers.h"
#include "serialize/serialize.h"
#include "server-socket.h"
#include "client-socket.h"
/*
 * A slab worker takes care of processing requests sent to the KV-Store.
 * E.g.:
 *    kv_add_async(...) results in a request being enqueued (enqueue_slab_callback function) into a slab worker
 *    The worker then dequeues the request, calls functions of slab.c to figure out where the item is on disk (or where it should be placed).
 *
 * Because we use async IO, the worker can enqueue/dequeue more callbacks while IOs are done by the drive (complete_processed_io(...)).
 *
 * A slab worker has its own slab, no other thread should touch the slab. This is straightforward in the current design: a worker sends IO requests
 * for its slabs and processes answers for its slab only.
 *
 * We have the following files on disk:
 *  If we have W disk workers per disk
 *  If we have S slab workers
 *  And Y disks
 *  Then we have W * S * Y files for any given item size:.
 *  /scratchY/slab-a-w-x = slab worker a, disk worker w, item size x on disk Y
 *
 * The slab.c functions abstract many disks into one, so
 *   /scratch** /slab-a-*-x  is the same virtual file
 * but it is a different slab from
 *   /scratch** /slab-b-*-x
 * To find in which slab to insert an element (i.e., which slab worker to use), we use the get_slab function bellow.
 */

static int nb_workers = 0;
static int nb_disks = 0;
static int nb_workers_launched = 0;
static int nb_workers_ready = 0;

int get_nb_workers(void) {
   return nb_workers;
}

int get_nb_disks(void) {
   return nb_disks;
}



/*
 * Worker context - Each worker thread in KVell has one of these structure
 */
size_t slab_sizes[] = { 100, 128, 256, 400, 512, 1024, 1365, 2048, 4096 };
struct slab_context {
   size_t worker_id __attribute__((aligned(64)));        // ID
   struct slab **slabs;                                  // Files managed by this worker
   struct slab_callback **callbacks;                     // Callbacks associated with the requests
   volatile size_t buffered_callbacks_idx;               // Number of requests enqueued or in the process of being enqueued
   volatile size_t sent_callbacks;                       // Number of requests fully enqueued
   volatile size_t processed_callbacks;                  // Number of requests fully submitted and processed on disk
   size_t max_pending_callbacks;                         // Maximum number of enqueued requests
   struct pagecache *pagecache __attribute__((aligned(64)));
   struct io_context *io_ctx;
   uint64_t rdt;                                         // Latest timestamp
} *slab_contexts;

static lru_entry*
de_serialize_lru(ser_buff_t *b){
  unsigned int sentinel = 0;
  SENTINEL_DETECTION_CODE(b);
  struct lru *lru_entry = calloc(1, sizeof(struct lru));
  de_serialize_data((char*)sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    lru->prev = NULL;
  }
  else{
    serialize_buffer_skip(b, -1*sizeof(unsigned int));
    lru_entry->prev = de_serialize_lru(b);
  }
  de_serialize_data((char*)sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    lru->next = NULL;
  }
  else{
    serialize_buffer_skip(b, -1*sizeof(unsigned int));
    lru_entry->next = de_serialize_lru(b);
  }
  de_serialize_data((char*)lru_entry->hash, b, sizeof(void));
  de_serialize_data((char*)lru_entry->contains_data, b, sizeof(int));
  de_serialize_data((char*)lru_entry->dirty, b, sizeof(int));
  return lru_entry;
}

static struct slab*
de_serialize_slabs(ser_buff_t *b){
  unsigned intsentinel = 0;
  struct slab *slabs = calloc(1, sizeof(slab));
  SENTINEL_DETECTION_CODE(b);
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->ctx = NULL;
  }
  else{
    serialize_buffer_skip(b, -1 * sizeof(unsigned int));
    slabs->ctx = calloc(1, sizeof(slab_context));
    slabs->ctx = de_serialize_ctx(b);
  }
  de_serialize_data((char*)slabs->item_size, b, sizeof(size_t));
  de_serialize_data((char*)slabs->nb_items, b, sizeof(size_t));
  de_serialize_data((char*)slabs->last_item, b, sizeof(size_t));
  de_serialize_data((char*)slabs->nb_max_items, b, sizeof(size_t));
  de_serialize_data((char*)slabs->fd, b, sizeof(int));
  de_serialize_data((char*)slabs->size_on_disk, b, sizeof(size_t));
  de_serialize_data((char*)slabs->nb_free_items, b, sizeof(size_t));
  de_serialize_data((char*)slabs->nb_free_items_in_memory, b, sizeof(size_t));
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->freed_items = NULL;
  }
  else{
    slabs->freed_items = calloc(1, sizeof(struct freelist_entry));
    slabs->freed_items = de_serialize_freed_items(b);
  }
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->freed_items_tail = NULL;
  }
  else{
    slabs->freed_items_tail = calloc(1, sizeof(struct freelist_entry));
    slabs->freed_items_tail = de_serialize_freed_items(b);
  }
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->freed_items_recovery = NULL;
  }
  else{
    slabs->freed_items_recovery = calloc(1, sizeof(btree_t));
    slabs->freed_items_recovery = de_serialize_freed_items_recovery(b);
  }
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->freed_items_pointed_to = NULL;
  }
  else{
    slabs->freed_items_pointed_to = calloc(1, sizeof(btree_t));
    slabs->freed_items_pointed_to = de_serialize_freed_items_recovery(b);
  }
}

static struct slab_callback*
de_serialize_callback(ser_buff_t *b){
  unsigned intsentinel = 0;
  SENTINEL_DETECTION_CODE(b);
  struct slab_callback *callback = calloc(1, sizeof(struct slab_callback));
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->ctx = NULL;
  }
  else{
    serialize_buffer_skip(b, -1 * sizeof(unsigned int));
    struct slab_cb_t *(callback->cb) = calloc(1, sizeof(slab_cb_t));
    de_serialize_data((char*)callback->cb, b, sizeof(slab_cb_t));
  }
  de_serialize_data((char*)callback->payload, b, sizeof(void));
  de_serialize_data((char*)callback->item, b, sizeof(void));
  de_serialize_data((char*)callback->action, b, sizeof(void));
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->slab = NULL;
  }
  else{
    serialize_buffer_skip(b, -1 * sizeof(unsigned int));
    callback->slab = calloc(1, sizeof(slab));
    callback->slab = de_serialize_slabs(b);
  }
  de_serialize_data((char*)callback->slab_idx, b, sizeof(uint64_t));
  de_serialize_data((char*)callback->tmp_page_number, b, sizeof(uint64_t));
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->lru_entry = NULL;
  }
  else{
    serialize_buffer_skip(b, -1 * sizeof(unsigned int));
    slabs->lru_entry = calloc(1, sizeof(struct lru));
    lru_entry = de_serialize_lru(b);
  }
  de_serialize_data((char*)&sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    slabs->io_cb = NULL;
  }
  else{
    serialize_buffer_skip(b, -1 * sizeof(unsigned int));
    callback->io_cb = calloc(1, sizeof(io_cb_t));
    de_serialize_data((char*)callback->cb, b, sizeof(slab_cb_t));
  }
  return callback;
}

static struct hash_t*
de_serialize_hash(ser_buff_t *b){

}

static struct pagecache*
de_serialize_page_cache(ser_buff_t *b){
  unsigned int sentinel = 0;
  SENTINEL_DETECTION_CODE(b);
  struct pagecache *page_cache = calloc(1, sizeof(pagecache));
  de_serialize_data((char*)page_cache->cached_data, b, PAGE_CACHE_SIZE/get_nb_workers());
  de_serialize_data((char*)sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    page_cache->hash_to_page = NULL;
  }
  else{
    serialize_buffer_skip(b, -1*sizeof(unsigned int));
    page_cache->hash_to_page = de_serialize_hash(b);
  }
  de_serialize_data((char*)sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    page_cache->used_pages = NULL;
  }
  else{
    serialize_buffer_skip(b, -1*sizeof(unsigned int));
    page_cache->used_pages = de_serialize_hash(b);
  }
  de_serialize_data((char*)sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    page_cache->oldest_pages = NULL;
  }
  else{
    serialize_buffer_skip(b, -1*sizeof(unsigned int));
    page_cache->oldest_pages = de_serialize_hash(b);
  }
  de_serialize_data((char*)sentinel, b, sizeof(unsigned int));
  if(sentinel == 0xFFFFFFFF){
    page_cache->newest_pages = NULL;
  }
  else{
    serialize_buffer_skip(b, -1*sizeof(unsigned int));
    page_cache->newest_pages = de_serialize_hash(b);
  }
  de_serialize_data((char*)page_cache->used_page_size, b, sizeof(size_t));
  return page_cache;
}

static struct io_context*
de_serialize_io_ctx(ser_buff_t *b){

}

static struct slab_context*
de_serialize_ctx(ser_buff_t *b){
  int loop_var;
  unsigned int sentinel = 0;
  SENTINEL_DETECTION_CODE(b);
  slab_context *ctx = calloc(1, sizeof(slab_context));
  de_serialize_data((char*)ctx->worker_id, b, sizeof(size_t));
  struct slab **slabs = de_serialize_slabs(b);
  struct slab_callback *callbacks = de_serialize_callback(b);
  de_serialize_data((char*)ctx->buffered_callbacks_idx, b, sizeof(size_t));
  de_serialize_data((char*)ctx->sent_callbacks, b, sizeof(size_t));
  de_serialize_data((char*)ctx->processed_callbacks, b, sizeof(size_t));
  de_serialize_data((char*)ctx->max_pending_callbacks, b, sizeof(size_t));
  struct pagecache *p = de_serialize_page_cache(b);
  struct io_context *io_ctx = de_serialize_io_ctx(b);
  de_serialize_data((char*)ctx->rdt, b, sizeof(uint64_t));

  return ctx;
}

/* A file is only managed by 1 worker. File => worker function. */
int get_worker(struct slab *s) {
   return s->ctx->worker_id;
}

struct pagecache *get_pagecache(struct slab_context *ctx) {
   return ctx->pagecache;
}

struct io_context *get_io_context(struct slab_context *ctx) {
   return ctx->io_ctx;
}

uint64_t get_rdt(struct slab_context *ctx) {
   return ctx->rdt;
}

void set_rdt(struct slab_context *ctx, uint64_t val) {
   ctx->rdt = val;
}

/*
 * When a request is submitted by a user, it is enqueued. Functions to do that.
 */

/* Get next available slot in a workers's context */
static size_t get_slab_buffer(struct slab_context *ctx) {
   size_t next_buffer = __sync_fetch_and_add(&ctx->buffered_callbacks_idx, 1);
   while(1) {
      volatile size_t pending = next_buffer - ctx->processed_callbacks;
      if(pending >= ctx->max_pending_callbacks) { // Queue is full, wait
         NOP10();
         if(!PINNING)
            usleep(2);
      } else {
         break;
      }
   }
   return next_buffer % ctx->max_pending_callbacks;
}

/* Once we get a slot, we fill it, and then submit it */
static size_t submit_slab_buffer(struct slab_context *ctx, int buffer_idx) {
   while(1) {
      if(ctx->sent_callbacks%ctx->max_pending_callbacks != buffer_idx) { // Somebody else is enqueuing a request, wait!
         NOP10();
      } else {
         break;
      }
   }
   return __sync_fetch_and_add(&ctx->sent_callbacks, 1);
}

static uint64_t get_hash_for_item(char *item) {
   struct item_metadata *meta = (struct item_metadata *)item;
   char *item_key = &item[sizeof(*meta)];
   return *(uint64_t*)item_key;
}

/* Requests are statically attributed to workers using this function */
static struct slab_context *get_slab_context(void *item) {
   uint64_t hash = get_hash_for_item(item);
   return &slab_contexts[hash%get_nb_workers()];
}

size_t get_item_size(char *item) {
   struct item_metadata *meta = (struct item_metadata *)item;
   return sizeof(*meta) + meta->key_size + meta->value_size;
}

static struct slab *get_slab(struct slab_context *ctx, void *item) {
   size_t item_size = get_item_size(item);
   for(size_t i = 0; i < sizeof(slab_sizes)/sizeof(*slab_sizes); i++) {
      if(item_size <= slab_sizes[i])
         return ctx->slabs[i];
   }
   die("Item is too big\n");
}

struct slab *get_item_slab(int worker_id, void *item) {
   struct slab_context *ctx = get_slab_context(item);
   return get_slab(ctx, item);
}

static void enqueue_slab_callback(struct slab_context *ctx, enum slab_action action, struct slab_callback *callback) {
   size_t buffer_idx = get_slab_buffer(ctx);
   callback->action = action;
   ctx->callbacks[buffer_idx] = callback;
   add_time_in_payload(callback, 0);
   submit_slab_buffer(ctx, buffer_idx);
   add_time_in_payload(callback, 1);
}

/*
 * KVell API - These functions are called from user context
 */
void *kv_read_sync(void *item) {
   struct slab_context *ctx = get_slab_context(item);
   struct slab *s = get_slab(ctx, item);
   // Warning, this is very unsafe, the lookup might not be performed in the worker context => race! We only use that during init.
   index_entry_t *e = memory_index_lookup(ctx->worker_id, item);
   if(e)
      return read_item(s, e->slab_idx);
   else
      return NULL;
}

void kv_read_async(struct slab_callback *callback) {
   struct slab_context *ctx = get_slab_context(callback->item);
   return enqueue_slab_callback(ctx, READ, callback);
}

void kv_read_async_no_lookup(struct slab_callback *callback, struct slab *s, size_t slab_idx) {
   callback->slab = s;
   callback->slab_idx = slab_idx;
   return enqueue_slab_callback(s->ctx, READ_NO_LOOKUP, callback);
}

void kv_add_async(struct slab_callback *callback) {
   struct slab_context *ctx = get_slab_context(callback->item);
   enqueue_slab_callback(ctx, ADD, callback);
}

void kv_update_async(struct slab_callback *callback) {
   struct slab_context *ctx = get_slab_context(callback->item);
   return enqueue_slab_callback(ctx, UPDATE, callback);
}

void kv_add_or_update_async(struct slab_callback *callback) {
   struct slab_context *ctx = get_slab_context(callback->item);
   return enqueue_slab_callback(ctx, ADD_OR_UPDATE, callback);
}

void kv_remove_async(struct slab_callback *callback) {
   struct slab_context *ctx = get_slab_context(callback->item);
   return enqueue_slab_callback(ctx, DELETE, callback);
}

tree_scan_res_t kv_init_scan(void *item, size_t scan_size) {
   return memory_index_scan(item, scan_size);
}

/*
 * Worker context
 */

/* Dequeue enqueued callbacks */
static void worker_dequeue_requests(struct slab_context *ctx) {
   size_t retries =  0;
   size_t sent_callbacks = ctx->sent_callbacks;
   size_t pending = sent_callbacks - ctx->processed_callbacks;
   if(pending == 0)
      return;
again:
   for(size_t i = 0; i < pending; i++) {
      struct slab_callback *callback = ctx->callbacks[ctx->processed_callbacks%ctx->max_pending_callbacks];
      enum slab_action action = callback->action;
      add_time_in_payload(callback, 2);

      index_entry_t *e = NULL;
      if(action != READ_NO_LOOKUP)
         e = memory_index_lookup(ctx->worker_id, callback->item);

      switch(action) {
         case READ_NO_LOOKUP:
            read_item_async(callback);
            break;
         case READ:
            if(!e) { // Item is not in DB
               callback->slab = NULL;
               callback->slab_idx = -1;
               callback->cb(callback, NULL);
            } else {
               callback->slab = e->slab;
               callback->slab_idx = e->slab_idx;
               read_item_async(callback);
            }
            break;
         case ADD:
            if(e) {
               die("Adding item that is already in the database! Use update instead! (This error might also appear if 2 keys have the same prefix, TODO: make index more robust to that.)\n");
            } else {
               callback->slab = get_slab(ctx, callback->item);
               callback->slab_idx = -1;
               add_item_async(callback);
            }
            break;
         case UPDATE:
            if(!e) {
               callback->slab = NULL;
               callback->slab_idx = -1;
               callback->cb(callback, NULL);
            } else {
               callback->slab = e->slab;
               callback->slab_idx = e->slab_idx;
               assert(get_item_size(callback->item) <= e->slab->item_size); // Item grew, this is not supported currently!
               update_item_async(callback);
            }
            break;
         case ADD_OR_UPDATE:
            if(!e) {
               callback->action = ADD;
               callback->slab = get_slab(ctx, callback->item);
               callback->slab_idx = -1;
               add_item_async(callback);
            } else {
               callback->action = UPDATE;
               callback->slab = e->slab;
               callback->slab_idx = e->slab_idx;
               assert(get_item_size(callback->item) <= e->slab->item_size); // Item grew, this is not supported currently!
               update_item_async(callback);
            }
         case DELETE:
            if(!e) {
               callback->slab = NULL;
               callback->slab_idx = -1;
               callback->cb(callback, NULL);
            } else {
               callback->slab = e->slab;
               callback->slab_idx = e->slab_idx;
               memory_index_delete(ctx->worker_id, callback->item);
               remove_item_async(callback);
            }
            break;
         default:
            die("Unknown action\n");
      }
      ctx->processed_callbacks++;
      if(NEVER_EXCEED_QUEUE_DEPTH && io_pending(ctx->io_ctx) >= QUEUE_DEPTH)
         break;
   }

   if(WAIT_A_BIT_FOR_MORE_IOS) {
      while(retries < 5 && io_pending(ctx->io_ctx) < QUEUE_DEPTH) {
         retries++;
         pending = ctx->sent_callbacks - ctx->processed_callbacks;
         if(pending == 0) {
            wait_for(10000);
         } else {
            goto again;
         }
      }
   }
}

static void worker_slab_init_cb(struct slab_callback *cb, void *item) {
   struct item_metadata *new_meta = item;
   if(!memory_index_lookup(get_worker(cb->slab), item)) {
      memory_index_add(cb, item);
   } else {
      /* Complex path -- item is already in the index, we should decide which one to keep based on rdt! */
      printf("#WARNING! Item is present twice in the database! Has the database crashed?\n");
      struct item_metadata *old_meta = kv_read_sync(item);
      assert(old_meta);

      if(old_meta->rdt < new_meta->rdt) {
         // TODO: the old spot should be added in the freelist
         btree_worker_delete(get_worker(cb->slab), old_meta);
         memory_index_add(cb, item);
      }

   }
}

static void *worker_slab_init(void *pdata) {
   struct slab_context *ctx = pdata;
   int socketfd, comm_socket_fd, data_socket, ret;
   unsigned int client_secret, result;
   fd_set readfds;
   char buffer[2048];

   server_struct_t *server_attribute = calloc(1, sizeof(server_struct_t*));
   if (argc != 2) {
         perror("ERROR, port is not initialized");
         exit(1);
   }
   in_port_t port = atoi(argv[1]);
   socketfd = init_socket_server(server_attribute);
   if(socketfd == -1){
         perror("Server-socket() error!");
         exit(0);
   }
   printf("Server-socket created\n");

   if(bind_create_socket(socketfd, port) < 0){
         perror("Server-socket-bind() failed");
         exit(0);
   }
   printf("bind done\n");

   if(listen(socketfd, 10) == -1){
     perror("Server-socket-listen() failed");
     exit(1);
   }
   add_to_monitor(server_attribute, socketfd);

   __sync_add_and_fetch(&nb_workers_launched, 1);

   pid_t x = syscall(__NR_gettid);
   printf("[SLAB WORKER %lu] tid %d\n", ctx->worker_id, x);
   pin_me_on(ctx->worker_id);

   /* Create the pagecache for the worker */
   ctx->pagecache = calloc(1, sizeof(*ctx->pagecache));
   page_cache_init(ctx->pagecache);

   /* Initialize the async io for the worker */
   ctx->io_ctx = worker_ioengine_init(ctx->max_pending_callbacks);

   /* Rebuild existing data structures */
   size_t nb_slabs = sizeof(slab_sizes)/sizeof(*slab_sizes);
   ctx->slabs = malloc(nb_slabs*sizeof(*ctx->slabs));
   struct slab_callback *cb = malloc(sizeof(*cb));
   cb->cb = worker_slab_init_cb;
   for(size_t i = 0; i < nb_slabs; i++) {
      ctx->slabs[i] = create_slab(ctx, ctx->worker_id, slab_sizes[i], cb);
   }
   free(cb);


   ser_buff_t *server_recv_ser_buffer = NULL;
   init_serialized_buffer_of_defined_size(&server_recv_ser_buffer, 2048);
   reset_serialize_buffer(server_recv_ser_buffer);
    __sync_add_and_fetch(&nb_workers_ready, 1);
    struct slab_context *received_ctx = calloc(1, sizeof(struct slab_context));
   /* Main loop: do IOs and process enqueued requests */
 declare_breakdown;
 while(1) {
    ctx->rdt++;

    while(io_pending(ctx->io_ctx)) {
       worker_ioengine_enqueue_ios(ctx->io_ctx); __1
       worker_ioengine_get_completed_ios(ctx->io_ctx); __2
       worker_ioengine_process_completed_ios(ctx->io_ctx); __3
    }

    volatile size_t pending = ctx->sent_callbacks - ctx->processed_callbacks;
    while(!pending && !io_pending(ctx->io_ctx)) {
       if(!PINNING) {
          usleep(2);
       } else {
          NOP10();
       }
       pending = ctx->sent_callbacks - ctx->processed_callbacks;
    } __4

    /* added piece of code for remote connection */
   for(;;){
     refresh(server_attribute, &readfds);
     printf("Waiting for incoming connection\n");
     select(get_max(server_attribute) + 1, &readfds, NULL, NULL, NULL);

     if(FD_ISSET(socketfd, &readfds)){                                           /* connection initiaztion part */
       printf("New connection recieved\n");
       data_socket = accept(socketfd, NULL, NULL);
       if(data_socket == -1){
         perror("accpet");
         exit(EXIT_FAILURE);
       }
       printf("connection accepted\n");
       add_to_monitor(server_attribute, data_socket);
     }
     else if(FD_ISSET(0, &readfds)){                                             /* input from console */
       char op[BUFFER_SIZE];
       ret = read(0, op, BUFFER_SIZE -1);
       op[strcspn(op, "\r\n")] = 0; // flush new line
       if(ret < 0){
           printf("Insert valid operation\n");
           break;
       }
       op[ret] = 0;
       printf("input from console:\n%s\n", op);
     }
     else{                                                   /* data strives on some other client's FDs. Find the client which has sent us the data request */
       for(int i=2; i< MAX_CLIENT_SUPPORTED; i++){
         if(FD_ISSET(get_monitored_fd_set(server_attribute, i), &readfds)){
           comm_socket_fd = get_monitored_fd_set(server_attribute, i);
           memset(buffer, 0, BUFFER_SIZE);
           ret = recv(comm_socket_fd, server_recv_ser_buffer->b, 2048, 0);
           if(ret == -1){
             perror("read");
             exit(0);
           }
           received_ctx = de_serialize_ctx(server_recv_ser_buffer);
           worker_dequeue_requests(received_ctx); __5 // Process queue
           show_breakdown_periodic(1000, received_ctx->processed_callbacks, "io_submit", "io_getevents", "io_cb", "wait", "slab_cb");
           /*ret = send(data_socket, &result, sizeof(int), 0);
           if(ret == -1){
             perror("read");
             exit(0);
           }*/
           close(comm_socket_fd);
           remove_from_monitor(server_attribute, comm_socket_fd);
           break;
         }
         break;
       }
     }
   }
 }
 close(socketfd);
 remove_from_monitor(server_attribute, socketfd);
 unlink(SOCKET_NAME);
 free(server_attribute);
 /* added piece of code for remote connection */
   return NULL;
}

void slab_workers_init(int _nb_disks, int nb_workers_per_disk) {
   size_t max_pending_callbacks = MAX_NB_PENDING_CALLBACKS_PER_WORKER;
   nb_disks = _nb_disks;
   nb_workers = nb_disks * nb_workers_per_disk;

   memory_index_init();

   pthread_t t;
   slab_contexts = calloc(nb_workers, sizeof(*slab_contexts));
   for(size_t w = 0; w < nb_workers; w++) {
      struct slab_context *ctx = &slab_contexts[w];
      ctx->worker_id = w;
      ctx->max_pending_callbacks = max_pending_callbacks;
      ctx->callbacks = calloc(ctx->max_pending_callbacks, sizeof(*ctx->callbacks));
      pthread_create(&t, NULL, worker_slab_init, ctx);
   }

   while(*(volatile int*)&nb_workers_ready != nb_workers) {
      NOP10();
   }
}

size_t get_database_size(void) {
   uint64_t size = 0;
   size_t nb_slabs = sizeof(slab_sizes)/sizeof(*slab_sizes);

   size_t nb_workers = get_nb_workers();
   for(size_t w = 0; w < nb_workers; w++) {
      struct slab_context *ctx = &slab_contexts[w];
      for(size_t i = 0; i < nb_slabs; i++) {
         size += ctx->slabs[i]->nb_items;
      }
   }

   return size;
}
