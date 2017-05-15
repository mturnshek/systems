/*
 * mm.c - 
 * Matthew Turnshek
 *           
 *          Segregated lists
 *          immediate-coalescing
 *          First-fit/Best-fit hybrid
 *          ~dynamic memory allocator~
 * 
 * 
 * The segregated list data structure has 8 free lists for the following size
 * size classes:
 *    <= 32,  <= 64,   <= 128,   <= 256 
 *    <= 512, <= 1024, <= 2048, larger
 * 
 * We traverse and manipulate our free lists with a series of helper functions,
 * including remove_free_block and insert_free_block.
 *
 * Each free block is formatted as such:
 *   header          payload                footer
 * [        ] [[id of prev] [id of next]] [         ]
 *  4 bytes       at least 8 bytes          4 bytes
 *
 * The reason why I can have payloads which are 8 bytes with segregated lists
 * is due to the fact that the heapsize is never greater than 2^32. This means
 * if we treat the base as the start of the heap, all 2^32 bytes are addressable
 * with only 4 bytes instead of 8. This makes things more memory efficient for
 * some processes.
 *
 * The best-fit/first-fit hybrid searches until it finds the first fit, and then
 * checks for a better fit for a few more blocks before choosing the current
 * current best-fitting block.
 * 
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

////////////
// Macros //
////////////

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/* Basic constants and macros */
#define WSIZE       4       /* Single word size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */

#define MIN_BLOCK_SIZE (WSIZE*4) 
                        // Used to make sure new blocks are at least
                        // this size.

#define NUM_SIZE_CLASSES 10 // Ten seglists

#define BLOCKS_PAST_FIRST_FIT 10 // We search a certain amount of blocks past
                                // our first fit, and choose the best from the
                                // group.

#define INITIAL_CHUNKSIZE  560
#define INCREASE_CHUNKSIZE 0

#define BINSIZE_0  32
#define BINSIZE_1  64
#define BINSIZE_2  128
#define BINSIZE_3  256
#define BINSIZE_4  512
#define BINSIZE_5  1024
#define BINSIZE_6  2048
#define BINSIZE_7  8192
#define BINSIZE_8  16384
#define BINSIZE_9  // This bin is the "else"

/////////////////////////////////
// Contract checking functions //
/////////////////////////////////

// Given a pointer, returns a bool 
// which is true if the pointer is within the heap's boundaries.
int in_heap(void* ptr) {
  size_t ptrvalue = (size_t)(ptr);
  size_t heaplo = (size_t)(mem_heap_lo());
  size_t heaphi = (size_t)(mem_heap_hi()) + sizeof(char*);
  return ((ptrvalue >= heaplo) && (ptrvalue <= heaphi));
}

// Given a pointer.
// Returns true if the pointer is aligned.
// Makes sure the minimum size is at least the minimum.
int is_aligned(void* ptr) {
  size_t ptrvalue = (size_t)(ptr);
  int aligned = ((ptrvalue % DSIZE) == 0);
  return aligned;
}

//////////////////////////////////////
// Structure manipulation functions //
//////////////////////////////////////

// Given a location, a size, and allocation, packs the values into that
// location. Used on headers and footers of blocks.
static inline void putpack(char* ptr, uint32_t size, uint32_t alloc) {
  REQUIRES(in_heap(ptr));
  *((uint32_t*)(ptr)) = (size | alloc);
}

// Given a header or footer, returns the size of the block.
static inline uint32_t getsize(char* ptr) {
  REQUIRES(in_heap(ptr));
  return *((uint32_t*)(ptr)) & ~((uint32_t)0x7);
}

// Given a header or footer, returns 1 if allocated and 0 if free.
static inline uint32_t getalloc(char* ptr) {
  REQUIRES(in_heap(ptr));
  return *((uint32_t*)(ptr)) & 0x1;
}

// Given a block pointer, returns the header pointer for that block.
static inline char* headerp(char* bp) {
  REQUIRES(is_aligned(bp));
  REQUIRES(in_heap(bp));
  return bp - WSIZE;
}

// Given a block pointer, returns the footer pointer for that block.
static inline char* footerp(char* bp) {
  REQUIRES(is_aligned(bp));
  REQUIRES(in_heap(bp));
  return bp + getsize(bp-WSIZE) - 2*WSIZE;
}

// Given a block pointer, returns the footer pointer of the previous block.
static inline char* prevblockinfo(char* bp) {
  REQUIRES(is_aligned(bp));
  REQUIRES(in_heap(bp));
  return bp - WSIZE*2;
}

// Given a block pointer, returns the header pointer of the next block.
static inline char* nextblockinfo(char* bp) {
  REQUIRES(is_aligned(bp));
  REQUIRES(in_heap(bp));
  return bp + getsize(bp-WSIZE) - WSIZE;
}

// Given a block pointer, returns the block pointer of the previous block.
static inline char* prevblock(char* bp) {
  REQUIRES(is_aligned(bp));
  REQUIRES(in_heap(bp));
  char* result = bp - getsize(prevblockinfo(bp));
  ENSURES(is_aligned(bp));
  ENSURES(in_heap(bp));
  return result;
}

// Given a block pointer, returns the block pointer of the next block.
static inline char* nextblock(char* bp) {
  REQUIRES(is_aligned(bp));
  REQUIRES(in_heap(bp));
  char* result = bp + getsize(bp-WSIZE);
  ENSURES(is_aligned(bp));
  ENSURES(in_heap(bp));
  return result;
}

//////////////////////////////
// Globals and declarations //
//////////////////////////////

// Global variables
char* start_of_heap; // We can use this to do a nifty memory optimization!
char* heap_listp;  // Pointer to prologue block
char* heap_endp; // Pointer to our epilogue block, end of the heap
void* seg_list_head; // The start of our array of segregated list heads.
                      // This is stored at the beginning of the heap.
size_t chunksize = INITIAL_CHUNKSIZE; // We need a global here because
                                      // the value is changing over time.

// Function declarations
void* get_next(void** ptr);
void* get_prev(void** ptr);
void set_next(void** ptr, void* new_address);
void set_prev(void** ptr, void* new_address);
void* coalesce(void* ptr);
void* extend_heap(size_t words);
int mm_init(void);
void* malloc(size_t malloc_size);
void* realloc(void *oldptr, size_t size);
void* calloc(size_t nmemb, size_t size);
int mm_checkheap(int verbose);
void place(size_t alloc_block_size, void* free_block_pointer);

///////////////////////////////
// Segregated list functions //
///////////////////////////////

/* 
 * getsizeclassnum - Takes a size_t size and returns the array index of the
 * size class which the size belongs to.
 */
int getsizeclassnum(size_t size) {
  if (size <= BINSIZE_0) {
    return 0;
  }
  else if (size <= BINSIZE_1) {
    return 1;
  }
  else if (size <= BINSIZE_2) {
    return 2;
  }
  else if (size <= BINSIZE_3) {
    return 3;
  }
  else if (size <= BINSIZE_4) {
    return 4;
  }
  else if (size <= BINSIZE_5) {
    return 5;
  }
  else if (size <= BINSIZE_6) {
    return 6;
  }
  else if (size <= BINSIZE_7) {
    return 7;
  }
  else if (size <= BINSIZE_8) {
    return 8;
  }
  else {
    return 9;
  }
}

/////////////////////////////
// Explicit list functions //
/////////////////////////////

// Contract function for checking whether a block is free.
// This necessarily includes it being aligned and being in the heap.
// This checks if the block's header and footer match and that the alloc
// bit is 0.
int is_free_block(void* ptr) {
  uint32_t header = *((uint32_t*)(headerp((char*)(ptr))));
  uint32_t footer = *((uint32_t*)(footerp((char*)(ptr))));
  return ((!getalloc(headerp((char*)(ptr)))) && (header == footer));
}


// Given a block ID in the form of a uint32_t, returns a pointer to that
// block. Since the heap will never be greater than 2^32 bytes, we can 
// effectively use "4 byte pointers" to increase memory utilization.
void* convert_4byte_to_heap_pointer(uint32_t fourbytepointer) {
  size_t first_half = ((size_t)start_of_heap & (0xFFFFFFFF00000000));
  size_t second_half = (size_t)fourbytepointer;
  void* result = (void*)(first_half | second_half);
  ENSURES(in_heap(result));
  ENSURES(is_aligned(result));
  return result;
}

// Given a heap pointer, converts it to a block ID which is 4 bytes.
// This is the inverse to the above function.
uint32_t convert_heap_pointer_to_4byte(void* heappointer) {
  REQUIRES(in_heap(heappointer));
  REQUIRES(is_aligned(heappointer));
  return (uint32_t) ((size_t)heappointer & 0x00000000FFFFFFFF);
}

// Given a pointer to a free block, gets the next free block in the FBL
void* get_next(void** ptr) {
  REQUIRES(is_free_block(ptr));
  uint32_t fourbytepointer = *((uint32_t*)(ptr) + 1); // Moving one wordsize up.
  void* result = convert_4byte_to_heap_pointer(fourbytepointer);
  return result;
}
// Given a pointer to a free block, gets the previous free block in the FBL
void* get_prev(void** ptr) {
  REQUIRES(is_free_block(ptr));
  uint32_t fourbytepointer = *((uint32_t*)(ptr));
  return convert_4byte_to_heap_pointer(fourbytepointer);
}

// Given a pointer to a free block, sets the next part of the data structure
// to the given address.
void set_next(void** ptr, void* new_address) {
  REQUIRES(is_free_block(ptr));
  *((uint32_t*)ptr + 1) = convert_heap_pointer_to_4byte(new_address);
}

// Given a pointer to a free block, sets the prev part of the data structure
// to the given address.
void set_prev(void** ptr, void* new_address) {
  REQUIRES(is_free_block(ptr));
  *((uint32_t*)ptr) = convert_heap_pointer_to_4byte(new_address);
}

/*
 * insert_free_block - Takes a free block and inserts it at the head
 * of the free list
 */ 
void insert_free_block(void* new_list_head) {
  REQUIRES(is_free_block(new_list_head));
  // There are three nodes we need to deal with here:
  // 1. the node we are inserting which is the new head
  // 2. the node which was "prev" the old head of the list
  // 3. the node which was the old head of the list
  // 

  // First let's grab the correct free list head for this block's size.
  int size_class_index = getsizeclassnum(getsize(headerp(new_list_head)));
  char** seg_list = (char**)(seg_list_head);

  // In the case where we have no free blocks, we only need to
  // reinitialize the free list!
  if (seg_list[size_class_index] == NULL) {
    seg_list[size_class_index] = (char*)new_list_head;
    set_prev(new_list_head, new_list_head);
    set_next(new_list_head, new_list_head);
  }
  // This is the normal case, where there is at least one free block.
  else {
    void* old_list_head = (void*)(seg_list[size_class_index]);

    // First let's deal with the new node.
    set_next(new_list_head, old_list_head);
    set_prev(new_list_head, (get_prev(old_list_head)));

    // Now let's deal with the "prev" of the old head.
    set_next(get_prev(old_list_head), new_list_head);

    // Finally, let's finish by setting the old list head's prev to the new head.
    set_prev(old_list_head, new_list_head);

    // Now we have to set our free list head to the new list head.
    seg_list[size_class_index] = (char*)new_list_head;
  }
}

/*
 * remove_free_block - Takes a block and removes it from its free list
 */
void remove_free_block(void* removed_block) {
  REQUIRES(is_free_block(removed_block));
  // There are two nodes we have to deal with here:
  // 1. The prev of the block we're removing
  // 2. The next of the block we're removing  

  // First let's grab the correct free list for this block's size.
  int size_class_index = getsizeclassnum(getsize(headerp(removed_block)));
  char** seg_list = (char**)(seg_list_head);

  // Let's check if the block we're removing is the head. If it
  // is, we switch its "next" section to be the head. This is so we don't
  // access it when it's not in the free list anymore by grabbing from the top.
  if (seg_list[size_class_index] == (char*)removed_block) {
    // If we only have one free block
    if ((char*)get_next((void*)seg_list[size_class_index])
                            == seg_list[size_class_index]) {
      seg_list[size_class_index] = NULL;
    }
    // If there is more than one block
    else {
      seg_list[size_class_index] =
        (char*)get_next((void*)seg_list[size_class_index]);
    }
  }
  // Now let's deal with the blocks we have to mess with.
  set_next(get_prev(removed_block), get_next(removed_block));
  set_prev(get_next(removed_block), get_prev(removed_block));
}

/////////////////////////////////////
// malloc package helper functions //
/////////////////////////////////////

/*
 * coalesce - Every time we call coalesce on a newly freed
 * block, we check if the blocks around it are free as well. Depending on
 * whether the blocks in question are free, we can merge with no blocks,
 * the previous block, the next block, or both surrounding blocks.
 * In this function we also remove blocks from their free lists which have
 * been merged.
 */
void* coalesce(void* free_block_pointer) { 
  char* previous_block_pointer;
  char* next_block_pointer;
  size_t prev_alloc = getalloc(prevblockinfo(free_block_pointer));
  size_t next_alloc = getalloc(nextblockinfo(free_block_pointer));

  // Size of our initial free block
  size_t size = getsize(headerp(free_block_pointer));

  // Case 1 - neither surrounding block is free
  if (prev_alloc && next_alloc) {
    return free_block_pointer; // In this case we don't have to merge.
  }

  // Case 2 - next block is free but not previous
  else if (prev_alloc && !next_alloc) {
    next_block_pointer = nextblock(free_block_pointer);
    // First, let's remove the free block ahead of us from the free list.
    remove_free_block(next_block_pointer);
    // Now we'll merge it with our free block.
    size += getsize(nextblockinfo(free_block_pointer));
    putpack(headerp(free_block_pointer), size, 0);
    putpack(footerp(free_block_pointer), size, 0);
    // Our free block pointer does not change in this case.
    return free_block_pointer;
  }

  // Case 3 - previous block is free but not next
  else if (!prev_alloc && next_alloc) {
    previous_block_pointer = prevblock(free_block_pointer);
    // First let's remove the free block behind us...
    remove_free_block(previous_block_pointer);
    // Now let's merge the two.
    size += getsize(prevblockinfo(free_block_pointer));
    putpack(footerp(free_block_pointer), size, 0);
    putpack(headerp(previous_block_pointer), size, 0);
    // This time we need to change the free_block pointer, since the payload
    // begins at a different place.
    return previous_block_pointer;
  }

  // Case 4 - both surrounding blocks are free
  else {
    previous_block_pointer = prevblock(free_block_pointer);
    next_block_pointer = nextblock(free_block_pointer);
    // In this case we need to remove both surrounding blocks.
    remove_free_block(previous_block_pointer);
    remove_free_block(next_block_pointer);
    // Now we merge with both.
    size += getsize(headerp(previous_block_pointer)) +
            getsize(headerp(next_block_pointer));
    putpack(headerp(previous_block_pointer), size, 0);
    putpack(footerp(next_block_pointer), size, 0);
    // We have to switch the block pointer because our payload position is
    // different.
    return previous_block_pointer;
  }
  // Control never reaches here.
  return free_block_pointer;
}


// Every time we increase the heap size, our chunksize will increase.
// This is a memory and throughput techinque that is very helpful!
void increase_chunksize() {
  chunksize += INCREASE_CHUNKSIZE;
}

// extend_heap - given a size, increases the amount of heapspace you can use
// by that amount and adds the new space to a free block which is placed in a
// corresponding seglist.
void* extend_heap(size_t size)  {
  char *ptr;

  if ((long)(ptr = mem_sbrk(size)) == -1) {
    return NULL;
  }

  // Creating the new free block
  putpack(headerp(ptr), size, 0);
  putpack(footerp(ptr), size, 0);

  heap_endp = nextblock(ptr); // Updating our end of heap
  putpack(headerp(heap_endp), DSIZE, 1); // New epilogue block

  return coalesce(ptr); // Eventually, malloc will add this block to the list.
}

// place - takes a size and an address and places a block there, potentially
// splitting. Place does not handle removing the given block from the free list,
// malloc does.
void place(size_t block_size, void* alloc_address) {
  size_t free_block_size = (getsize(headerp(alloc_address)));

  // If we split...
  if ((free_block_size - block_size) >= MIN_BLOCK_SIZE) {
    putpack(headerp(alloc_address), block_size, 1);
    putpack(footerp(alloc_address), block_size, 1);
    alloc_address = nextblock(alloc_address);
    putpack(headerp(alloc_address), free_block_size-block_size, 0);
    putpack(footerp(alloc_address), free_block_size-block_size, 0);
    // Then we have to insert our new block into the free list
    insert_free_block(alloc_address);
  }
  else {
    putpack(headerp(alloc_address), free_block_size, 1);
    putpack(footerp(alloc_address), free_block_size, 1);
  }
}

///////////////////////////////////
// malloc package main functions //
///////////////////////////////////

/*
 * mm_init - Called when a new trace starts.
 * In this function we initialize the free lists and reset the heap conditions.
 */
int mm_init(void) {
    void* first_block;
    char** seg_list;

    // First, reinitialize the chunksize for heaps.
    chunksize = INITIAL_CHUNKSIZE;
 
    /* Create the initial empty heap */
    // 10*DSIZE for segregated list pointers.
    // 4*WSIZE for padding, prologue, and epilogue blocks.
    if ((heap_listp = mem_sbrk(10*DSIZE + 4*WSIZE)) == (void *)-1) {
      return -1;
    }

    // A pointer to the start of the heap is used for a memory optimization,
    // which we can do since the heap will not be bigger than 2^32.
    start_of_heap = heap_listp;

    putpack(heap_listp, 0, 0); // Padding at the beginning

    // We "allocate" our segregated list heads at the start of the heap.
    // For now this means not putting anything there. Blocks will be inserted
    // into the correct free list in insert_free_block.
    seg_list_head = (void*)(heap_listp);
    seg_list = (char**)seg_list_head;
    seg_list[0] = NULL;
    seg_list[1] = NULL;
    seg_list[2] = NULL;
    seg_list[3] = NULL;
    seg_list[4] = NULL;
    seg_list[5] = NULL;
    seg_list[6] = NULL;
    seg_list[7] = NULL;
    seg_list[8] = NULL;
    seg_list[9] = NULL;

    putpack(heap_listp + (10*DSIZE + 1*WSIZE), 2*WSIZE, 1); // Prologue header 
    putpack(heap_listp + (10*DSIZE + 2*WSIZE), 2*WSIZE, 1); // Prologue footer 
    putpack(heap_listp + (10*DSIZE + 3*WSIZE), DSIZE, 1);  // Epilogue header
    heap_listp += (10*DSIZE + 2*WSIZE); // Points to prologue block
    heap_endp = nextblock(heap_listp);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if ((first_block = extend_heap(chunksize)) == NULL) {
      return -1;
    }

    set_prev(first_block, first_block);
    set_next(first_block, first_block);
    insert_free_block(first_block);
    return 0;
}

/*
 * malloc - Given an amount of memory, returns a pointer to the beginning of
 * an allocated chunk of memory that is at least as big as you requested.
 * 
 * This particular malloc implementation uses segregated lists, and a
 * first-fit/best-fit hybrid that works as follows:
 *    1. Find the first fit
 *    2. Continue searching for a better fit until you have
 *       searched BLOCKS_PAST_FIRST_FIT blocks, or reached the end of your
 *       current segregated list.
 *    3. Allocate and return a pointer to the best-fitting block.
 */
void *malloc(size_t malloc_size) {
  size_t new_size; // Adjusted block size (alignment)
  int size_class_index;
  void* new_free_block;
  char** seg_list = (char**)seg_list_head;
  char* initial_head;
  char* best_fit;
  int i;
  int found_first;
  int amt_after_first;

  checkheap(4); // We also checkheap just before malloc eventually returns.

  // Accounting for alignment and the header and footer sizes
  new_size = DSIZE * ((malloc_size + (2*WSIZE) + (DSIZE-1)) / DSIZE);
  if (new_size < MIN_BLOCK_SIZE) {
    new_size = MIN_BLOCK_SIZE;
  }

  // Now get the size class index to start.
  size_class_index = getsizeclassnum(new_size);

  // We start our search at the first size class it could belong to.
  char* current_free_blockp = seg_list[size_class_index];

  for (i = size_class_index; (i < (NUM_SIZE_CLASSES)); i++) {
    current_free_blockp = seg_list[i];
    initial_head = current_free_blockp;
    best_fit = NULL;
    found_first = 0; // used as bool. 
    amt_after_first = 0;
    // If current_free_blockp is NULL, that means we don't have any blocks in
    // our free list.
    if (current_free_blockp == NULL) {
      // If we're at the max size class already extend heap...
      if (i == NUM_SIZE_CLASSES-1) {
        new_free_block = extend_heap(chunksize);
        increase_chunksize(); // Increase each time...
        insert_free_block(new_free_block);
        return malloc(malloc_size);
      }
      // Otherwise reloop (and increment).
      else {
        continue;
      }
    }

    // We use a do loop here because we certainly want to search at least one
    // free block.
    do {
      // If the block is large enough, we'll place it.
      if (getsize(headerp(current_free_blockp)) >= new_size) {
        if (best_fit == NULL) {
          best_fit = current_free_blockp;
          found_first = 1;
        }
        else if (getsize(headerp(best_fit)) >
                 getsize(headerp(current_free_blockp))) {
          best_fit = current_free_blockp;
        }
      }
      if (found_first) {
        amt_after_first++;
      }
      if (amt_after_first >= BLOCKS_PAST_FIRST_FIT) {
        // First we need to remove it from the free list.
        remove_free_block(best_fit);
        // Then we'll place it. This function also does splitting.
        place(new_size, best_fit);
        checkheap(4);
        return best_fit;
      }
      // otherwise move on to the next free block
      current_free_blockp = (char*) get_next((void**)current_free_blockp);
    } while (current_free_blockp != initial_head);

    // After searching that seglist, do the best fit.
    if (best_fit != NULL) {
      // First we need to remove it from the free list.
      remove_free_block(best_fit);
      // Then we'll place it. This function also does splitting.
      place(new_size, best_fit);
      checkheap(4);
      return best_fit;
    }
  }

  // If we reached the end of the loop and didn't find a free block, that means
  // we need more space. Extend the heap!
  new_free_block = extend_heap(chunksize);
  increase_chunksize(); // Increase each time we extend
  insert_free_block(new_free_block);
  return malloc(malloc_size);
}

/*
 * free - Frees an allocated block by unsetting the allocated bit on its
 * header and footer. Uses explicit lists, so when freeing a block sets
 * pointers where the payload was to point to the previous and next
 * free blocks. Immediately coalesces with the surrounding blocks when freeing
 * a block.
 */
void free(void *ptr) {
  // REQUIRES the block is allocated
  void* new_free_block;

  checkheap(4);

  if(ptr == 0) { 
    return;
  }

  size_t size = getsize(headerp(ptr));

  // We have to change the header and footer to say "free!"
  // Change the header block to its size and "unallocated"
  putpack(headerp(ptr), size, 0);
  putpack(footerp(ptr), size, 0);

  
  new_free_block = coalesce(ptr);

  insert_free_block(new_free_block);

  checkheap(4);
}

/*
 * realloc - Change the size of a previously allocated block.
 */
void *realloc(void *oldptr, size_t size) {
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  newptr = malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  oldsize = *SIZE_PTR(oldptr);
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  free(oldptr);

  return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/////////////////////////
// Debugging functions //
/////////////////////////

/*
 * displayHeap - debugging and visualization function. Displays the heap in
 * text format where each block is shown as "FREE" or "ALLOC" with a size,
 * for example -ALLOC16--FREE1024--ALLOC8-
 */
void displayHeap() {
  char* current_pointer = heap_listp;
  while (1) {
    current_pointer = nextblock(current_pointer);
    if (getalloc(headerp(current_pointer))) {
      dbg_printf("-ALLOC%u-", getsize(headerp(current_pointer)));
    }
    else {
      dbg_printf("-FREE%u-", getsize(headerp(current_pointer)));
    }
    if (getsize(headerp(current_pointer)) <= DSIZE) {
      dbg_printf("\n");
      break;
    }
  }
}

/*
 * displayFreeLists - debugging and visualization function. Displays the 8
 * free lists of the different size classes, where each block is shown as
 * -[size]-. If there are no blocks in a free list, NULL is displayed.
 */
void displayFreeLists() {
  char* current_pointer;
  char* initial_head;
  for (int i = 0; (i < NUM_SIZE_CLASSES); i++) {
    dbg_printf("%d) ", i);
    current_pointer = ((char**)seg_list_head)[i];
    initial_head = current_pointer;
    if (current_pointer == NULL) {
      dbg_printf("NULL\n");
      continue;
    }
    do {
      dbg_printf("[%u]", getsize(headerp(current_pointer)));
      current_pointer = (char*)get_next((void**)current_pointer);
    } while (current_pointer != initial_head);
    dbg_printf("\n");
  }
}

// Given a block pointer, returns 1 unless it is both free and there is a free
// block around it.
int no_coalesce_available(char* bp) {
  if (getalloc(headerp(bp)) == 0) {
    return ((getalloc(nextblockinfo(bp))) && (getalloc(prevblockinfo(bp))));
  } 
  return 1;
}

/*
 * mm_checkheap - Different levels correspond to different checks.
 * Level one checks the prologue and epilogue blocks.
 * Level two checks the explicit free list for consistency.
 * Level three checks each block to make sure its header and footer are equal.
 * Level four displays an ASCII heap.
 */
int mm_checkheap(int verbose) {
  void* current_block;
  int amount_of_free_blocks_lists = 0;
  int amount_of_free_blocks_heap = 0;
  void* initial_head;
  //int amount_of_free_blocks;
  if (verbose >= 1) {
    // First check prologue block
    ASSERT(getsize(headerp(heap_listp)) == 2*WSIZE);
    ASSERT(getsize(footerp(heap_listp)) == 2*WSIZE);
    ASSERT(getalloc(headerp(heap_listp)) == 1);
    ASSERT(getalloc(footerp(heap_listp)) == 1);
    // End prologue block tests

    // Now check epilogue block
    ASSERT(getsize(headerp(heap_endp)) == DSIZE);
    ASSERT(getalloc(headerp(heap_endp)) == 1);
  }
  // Check the free lists for their invariants.
  // 
  if (verbose >= 2) {
    // Iterate over our size classes.
    for (int i = 0; (i < NUM_SIZE_CLASSES); i++) {
      current_block = ((void**)seg_list_head)[i];
      initial_head = current_block;

      if (current_block == NULL) {
        continue;
      }

      do {
        amount_of_free_blocks_lists++;
        ASSERT(in_heap(current_block));
        ASSERT(get_prev(get_next(current_block)) == current_block);
        current_block = get_next(current_block);
        ASSERT(get_next(get_prev(current_block)) == current_block);
      } while (current_block != initial_head);
    }
  }
  // Check each block in the heap, to make sure the header and footer match.
  // Also checks the next and previous block pointer macros.
  // Makes sure each block is above the minimum size.
  // Makes sure there are no two free blocks next to each other (coalescing)
  if (verbose >= 3) {
    current_block = nextblock(heap_listp);
    while (current_block != heap_endp) {
      if (!getalloc(headerp(current_block))) {
        amount_of_free_blocks_heap++;
      }
      if(getsize(headerp(current_block)) != getsize(footerp(current_block))) {
        dbg_printf("%p (hd) size not the same as %p (ft) for %p (bp).\n",
                headerp(current_block), footerp(current_block), current_block);
        ASSERT(0);
      }
      if(getalloc(headerp(current_block)) != getalloc(footerp(current_block))) {
        dbg_printf("%p (hd) alloc not the same as %p (ft) for %p (bp).\n",
                headerp(current_block), footerp(current_block), current_block);
        ASSERT(0);
      }
      if(getsize(headerp(current_block)) < MIN_BLOCK_SIZE) {
        dbg_printf("%p smaller than minimum size\n", current_block);
        ASSERT(0);
      }
      ASSERT(in_heap(current_block));
      ASSERT(is_aligned(current_block));
      ASSERT(no_coalesce_available(current_block));
      ASSERT(prevblock(nextblock(current_block)) == current_block);
      current_block = nextblock((char*)current_block);
    }
  }
  // Make sure that the number of free blocks in the free lists is
  // equal to the number of free blocks in the entire heap.
  if (verbose >= 4) {
    if (amount_of_free_blocks_heap != amount_of_free_blocks_lists) {
      dbg_printf("heap:%d lists:%d\n", amount_of_free_blocks_heap,
                                       amount_of_free_blocks_lists);
      ASSERT(0);
    }
  }
  return 0;
}