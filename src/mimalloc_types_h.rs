/* ----------------------------------------------------------------------------
Copyright (c) 2018-2021, Microsoft Research, Daan Leijen
This is free software; you can redistribute it and/or modify it under the
terms of the MIT license. A copy of the license can be found in the file
"LICENSE" at the root of this distribution.
-----------------------------------------------------------------------------*/

use std::mem::size_of;
use c2rust_bitfields::BitfieldStruct;

// Minimal alignment necessary. On most platforms 16 bytes are needed
// due to SSE registers for example. This must be at least `sizeof(void*)`
// FIXME
const MI_MAX_ALIGN_SIZE: u64 = 16;   // sizeof(max_align_t)

// ------------------------------------------------------
// Platform specific values
// ------------------------------------------------------

// FIXME: Should be in `Memory`, from `Address` type:
const MI_INTPTR_SHIFT: usize = size_of::<u64>().ilog2();
const MI_SIZE_SHIFT: usize = size_of::<u64>().ilog2();
const MI_INTPTR_SIZE: usize = size_of::<u64>();
const MI_SIZE_SIZE: usize = size_of::<u64>();
const MI_INTPTR_BITS: usize = u64::BITS;
const MI_SIZE_BITS: usize = u64::BITS;

const MI_KiB: u64 = 1024;
const MI_MiB: u64 = MI_KiB*MI_KiB;
const MI_GiB: u64 = MI_MiB*MI_KiB;


// ------------------------------------------------------
// Main internal data-structures
// ------------------------------------------------------

// Main tuning parameters for segment and page sizes
// Sizes for 64-bit (usually divide by two for 32-bit)
const MI_SEGMENT_SLICE_SHIFT: usize = 13 + MI_INTPTR_SHIFT;         // 64KiB  (32KiB on 32-bit)

const MI_SEGMENT_SHIFT: usize = if MI_INTPTR_SIZE > 4 {
  9 + MI_SEGMENT_SLICE_SHIFT)  // 32MiB
} else {
  7 + MI_SEGMENT_SLICE_SHIFT)  // 4MiB on 32-bit
}

const MI_SMALL_PAGE_SHIFT: usize = MI_SEGMENT_SLICE_SHIFT;       // 64KiB
const MI_MEDIUM_PAGE_SHIFT: usize = 3 + MI_SMALL_PAGE_SHIFT;     // 512KiB


// Derived constants
const MI_SEGMENT_SIZE: usize = 1usize<<MI_SEGMENT_SHIFT;
const MI_SEGMENT_ALIGN = MI_SEGMENT_SIZE;
const MI_SEGMENT_MASK: usize = MI_SEGMENT_ALIGN - 1;
const MI_SEGMENT_SLICE_SIZE: usize = 1usize << MI_SEGMENT_SLICE_SHIFT;
const MI_SLICES_PER_SEGMENT: usize = MI_SEGMENT_SIZE / MI_SEGMENT_SLICE_SIZE; // 1024

const MI_SMALL_PAGE_SIZE: usize = 1usize<<MI_SMALL_PAGE_SHIFT;
const MI_MEDIUM_PAGE_SIZE: usize = 1usize<<MI_MEDIUM_PAGE_SHIFT;

const MI_SMALL_OBJ_SIZE_MAX: usize = MI_SMALL_PAGE_SIZE/4;   // 8KiB on 64-bit
const MI_MEDIUM_OBJ_SIZE_MAX: usize = MI_MEDIUM_PAGE_SIZE/4;  // 128KiB on 64-bit
const MI_MEDIUM_OBJ_WSIZE_MAX: usize = MI_MEDIUM_OBJ_SIZE_MAX/MI_INTPTR_SIZE;
const MI_LARGE_OBJ_SIZE_MAX: usize = MI_SEGMENT_SIZE/2;      // 32MiB on 64-bit
const MI_LARGE_OBJ_WSIZE_MAX: usize = MI_LARGE_OBJ_SIZE_MAX/MI_INTPTR_SIZE;

// Maximum number of size classes. (spaced exponentially in 12.5% increments)
const MI_BIN_HUGE: usize = 73;

const _unused1: () = if MI_MEDIUM_OBJ_WSIZE_MAX >= 655360 {
  compile_error!("mimalloc internal: define more bins")
};

// Maximum slice offset (15)
const MI_MAX_SLICE_OFFSET: usize = (MI_ALIGNMENT_MAX / MI_SEGMENT_SLICE_SIZE) - 1;

// Used as a special value to encode block sizes in 32 bits.
const MI_HUGE_BLOCK_SIZE: u32 = (2*MI_GiB);

// blocks up to this size are always allocated aligned
const MI_MAX_ALIGN_GUARANTEE: usize = 8*MI_MAX_ALIGN_SIZE;

// Alignments over MI_ALIGNMENT_MAX are allocated in dedicated huge page segments 
const MI_ALIGNMENT_MAX: usize = MI_SEGMENT_SIZE >> 1;


// ------------------------------------------------------
// Mimalloc pages contain allocated blocks
// ------------------------------------------------------

// The free lists use encoded next fields
// (Only actually encodes when MI_ENCODED_FREELIST is defined.)
type mi_encoded_t = u64; // FIXME: Use `Address` instead.

// thread id's
type mi_threadid_t = u64; // FIXME: Use `Size` instead.

// free lists contain blocks
struct mi_block_t {
  mi_encoded_t next;
}


// The delayed flags are used for efficient multi-threaded free-ing
enum mi_delayed_t {
  MI_USE_DELAYED_FREE   = 0, // push on the owning heap thread delayed list
  MI_DELAYED_FREEING    = 1, // temporary: another thread is accessing the owning heap
  MI_NO_DELAYED_FREE    = 2, // optimize: push on page local thread free queue if another block is already in the heap thread delayed free list
  MI_NEVER_DELAYED_FREE = 3, // sticky, only resets on page reclaim
};


// The `in_full` and `has_aligned` page flags are put in a union to efficiently
// test if both are false (`full_aligned == 0`) in the `mi_free` routine.
// TODO
// union mi_page_flags_t {
//   pub full_aligned: u8,
//   pub x: mi_page_flags_bits_t,
// }

// Thread free list.
// We use the bottom 2 bits of the pointer for mi_delayed_t flags
type mi_thread_free_t = u64;

// A page contains blocks of one specific size (`block_size`).
// Each page has three list of free blocks:
// `free` for blocks that can be allocated,
// `local_free` for freed blocks that are not yet available to `mi_malloc`
// `thread_free` for freed blocks by other threads
// The `local_free` and `thread_free` lists are migrated to the `free` list
// when it is exhausted. The separate `local_free` list is necessary to
// implement a monotonic heartbeat. The `thread_free` list is needed for
// avoiding atomic operations in the common case.
//
//
// `used - |thread_free|` == actual blocks that are in use (alive)
// `used - |thread_free| + |free| + |local_free| == capacity`
//
// We don't count `freed` (as |free|) but use `used` to reduce
// the number of memory accesses in the `mi_page_all_free` function(s).
//
// Notes:
// - Access is optimized for `mi_free` and `mi_page_alloc` (in `alloc.c`)
// - Using `uint16_t` does not seem to slow things down
// - The size is 8 words on 64-bit which helps the page index calculations
//   (and 10 words on 32-bit, and encoded free lists add 2 words. Sizes 10
//    and 12 are still good for address calculation)
// - To limit the structure size, the `xblock_size` is 32-bits only; for
//   blocks > MI_HUGE_BLOCK_SIZE the size is determined from the segment page size
// - `thread_free` uses the bottom bits as a delayed-free flags to optimize
//   concurrent frees where only the first concurrent free adds to the owning
//   heap `thread_delayed_free` list (see `alloc.c:mi_free_block_mt`).
//   The invariant is that no-delayed-free is only set if there is
//   at least one block that will be added, or as already been added, to
//   the owning heap `thread_delayed_free` list. This guarantees that pages
//   will be freed correctly even if only other threads free blocks.
#[derive(BitfieldStruct)]
struct mi_page_flags_t {
  #[bitfield(name = "is_reset", ty = "bool", bits = "0..=0")] // `true` if the page memory was reset
  #[bitfield(name = "is_committed", ty = "bool", bits = "1..=1")] // `true` if the page virtual memory is committed
  #[bitfield(name = "is_zero_init", ty = "bool", bits = "2..=2")] // `true` if the page was zero initialized
  #[bitfield(name = "is_zero", ty = "bool", bits = "3..=3")] // `true` if the blocks in the free list are zero initialized
  #[bitfield(name = "in_full", ty = "bool", bits = "4..=4")]
  #[bitfield(name = "has_aligned", ty = "bool", bits = "5..=5")]
  bits: [u8; 1],
}

struct mi_page_t {
  bits: mi_page_flags_bits_t,
  // "owned" by the segment
  slice_count: u32,       // slices in this page (0 if not a page)
  slice_offset: u32,      // distance from the actual page data slice (0 if a page)

  // layout like this to optimize access in `mi_malloc` and `mi_free`
  capacity: u16,          // number of blocks committed, must be the first field, see `segment.c:page_clear`
  reserved: u16,          // number of blocks reserved in memory
  retire_expire: u8, // expiration count for retired blocks (in C code it was 7-bit bitfield)

  free: Address<mi_block_t>,              // list of available free blocks (`malloc` allocates from this list)
  used: u32,              // number of blocks in use (including blocks in `local_free` and `thread_free`)
  xblock_size: u32,       // size available in each block (always `>0`)
  local_free: Address<mi_block_t>,        // list of deferred free blocks by this thread (migrates to `free`)

  #[cfg(mi_encode_freelist)]
  keys: [u64; 2],           // two random keys to encode the free lists (see `_mi_block_next`)

////////////////////////////////////////////////////////////////////////////////////////////////////
  _Atomic(mi_thread_free_t) xthread_free;  // list of deferred free blocks freed by other threads
  _Atomic(uintptr_t)        xheap;

  struct mi_page_s*     next;              // next page owned by this thread with the same `block_size`
  struct mi_page_s*     prev;              // previous page owned by this thread with the same `block_size`

  // 64-bit 9 words, 32-bit 12 words, (+2 for secure)
  #if MI_INTPTR_SIZE==8
  uintptr_t padding[1];
  #endif
} ;



typedef enum mi_page_kind_e {
  MI_PAGE_SMALL,    // small blocks go into 64KiB pages inside a segment
  MI_PAGE_MEDIUM,   // medium blocks go into medium pages inside a segment
  MI_PAGE_LARGE,    // larger blocks go into a page of just one block
  MI_PAGE_HUGE,     // huge blocks (> 16 MiB) are put into a single page in a single segment.
} mi_page_kind_t;

typedef enum mi_segment_kind_e {
  MI_SEGMENT_NORMAL, // MI_SEGMENT_SIZE size with pages inside.
  MI_SEGMENT_HUGE,   // > MI_LARGE_SIZE_MAX segment with just one huge page inside.
} mi_segment_kind_t;

// ------------------------------------------------------
// A segment holds a commit mask where a bit is set if
// the corresponding MI_COMMIT_SIZE area is committed.
// The MI_COMMIT_SIZE must be a multiple of the slice
// size. If it is equal we have the most fine grained 
// decommit (but setting it higher can be more efficient).
// The MI_MINIMAL_COMMIT_SIZE is the minimal amount that will
// be committed in one go which can be set higher than
// MI_COMMIT_SIZE for efficiency (while the decommit mask
// is still tracked in fine-grained MI_COMMIT_SIZE chunks)
// ------------------------------------------------------

#define MI_MINIMAL_COMMIT_SIZE      (16*MI_SEGMENT_SLICE_SIZE)           // 1MiB
#define MI_COMMIT_SIZE              (MI_SEGMENT_SLICE_SIZE)              // 64KiB
#define MI_COMMIT_MASK_BITS         (MI_SEGMENT_SIZE / MI_COMMIT_SIZE)  
#define MI_COMMIT_MASK_FIELD_BITS    MI_SIZE_BITS
#define MI_COMMIT_MASK_FIELD_COUNT  (MI_COMMIT_MASK_BITS / MI_COMMIT_MASK_FIELD_BITS)

#if (MI_COMMIT_MASK_BITS != (MI_COMMIT_MASK_FIELD_COUNT * MI_COMMIT_MASK_FIELD_BITS))
#error "the segment size must be exactly divisible by the (commit size * size_t bits)"
#endif

typedef struct mi_commit_mask_s {
  size_t mask[MI_COMMIT_MASK_FIELD_COUNT];
} mi_commit_mask_t;

typedef mi_page_t  mi_slice_t;
typedef int64_t    mi_msecs_t;


// Segments are large allocated memory blocks (8mb on 64 bit) from
// the OS. Inside segments we allocated fixed size _pages_ that
// contain blocks.
typedef struct mi_segment_s {
  size_t            memid;              // memory id for arena allocation
  bool              mem_is_pinned;      // `true` if we cannot decommit/reset/protect in this memory (i.e. when allocated using large OS pages)    
  bool              mem_is_large;       // in large/huge os pages?
  bool              mem_is_committed;   // `true` if the whole segment is eagerly committed
  size_t            mem_alignment;      // page alignment for huge pages (only used for alignment > MI_ALIGNMENT_MAX)
  size_t            mem_align_offset;   // offset for huge page alignment (only used for alignment > MI_ALIGNMENT_MAX)

  bool              allow_decommit;     
  mi_msecs_t        decommit_expire;
  mi_commit_mask_t  decommit_mask;
  mi_commit_mask_t  commit_mask;

  _Atomic(struct mi_segment_s*) abandoned_next;

  // from here is zero initialized
  struct mi_segment_s* next;            // the list of freed segments in the cache (must be first field, see `segment.c:mi_segment_init`)
  
  size_t            abandoned;          // abandoned pages (i.e. the original owning thread stopped) (`abandoned <= used`)
  size_t            abandoned_visits;   // count how often this segment is visited in the abandoned list (to force reclaim it it is too long)
  size_t            used;               // count of pages in use
  uintptr_t         cookie;             // verify addresses in debug mode: `mi_ptr_cookie(segment) == segment->cookie`  

  size_t            segment_slices;      // for huge segments this may be different from `MI_SLICES_PER_SEGMENT`
  size_t            segment_info_slices; // initial slices we are using segment info and possible guard pages.

  // layout like this to optimize access in `mi_free`
  mi_segment_kind_t kind;
  size_t            slice_entries;       // entries in the `slices` array, at most `MI_SLICES_PER_SEGMENT`
  _Atomic(mi_threadid_t) thread_id;      // unique id of the thread owning this segment

  mi_slice_t        slices[MI_SLICES_PER_SEGMENT+1];  // one more for huge blocks with large alignment
} mi_segment_t;


// ------------------------------------------------------
// Heaps
// Provide first-class heaps to allocate from.
// A heap just owns a set of pages for allocation and
// can only be allocate/reallocate from the thread that created it.
// Freeing blocks can be done from any thread though.
// Per thread, the segments are shared among its heaps.
// Per thread, there is always a default heap that is
// used for allocation; it is initialized to statically
// point to an empty heap to avoid initialization checks
// in the fast path.
// ------------------------------------------------------

// Thread local data
typedef struct mi_tld_s mi_tld_t;

// Pages of a certain block size are held in a queue.
typedef struct mi_page_queue_s {
  mi_page_t* first;
  mi_page_t* last;
  size_t     block_size;
} mi_page_queue_t;

#define MI_BIN_FULL  (MI_BIN_HUGE+1)

// Random context
typedef struct mi_random_cxt_s {
  uint32_t input[16];
  uint32_t output[16];
  int      output_available;
  bool     weak;
} mi_random_ctx_t;


// In debug mode there is a padding structure at the end of the blocks to check for buffer overflows
#if (MI_PADDING)
typedef struct mi_padding_s {
  uint32_t canary; // encoded block value to check validity of the padding (in case of overflow)
  uint32_t delta;  // padding bytes before the block. (mi_usable_size(p) - delta == exact allocated bytes)
} mi_padding_t;
#define MI_PADDING_SIZE   (sizeof(mi_padding_t))
#define MI_PADDING_WSIZE  ((MI_PADDING_SIZE + MI_INTPTR_SIZE - 1) / MI_INTPTR_SIZE)
#else
#define MI_PADDING_SIZE   0
#define MI_PADDING_WSIZE  0
#endif

#define MI_PAGES_DIRECT   (MI_SMALL_WSIZE_MAX + MI_PADDING_WSIZE + 1)


// A heap owns a set of pages.
struct mi_heap_s {
  mi_tld_t*             tld;
  mi_page_t*            pages_free_direct[MI_PAGES_DIRECT];  // optimize: array where every entry points a page with possibly free blocks in the corresponding queue for that size.
  mi_page_queue_t       pages[MI_BIN_FULL + 1];              // queue of pages for each size class (or "bin")
  _Atomic(mi_block_t*)  thread_delayed_free;
  mi_threadid_t         thread_id;                           // thread this heap belongs too
  mi_arena_id_t         arena_id;                            // arena id if the heap belongs to a specific arena (or 0)  
  uintptr_t             cookie;                              // random cookie to verify pointers (see `_mi_ptr_cookie`)
  uintptr_t             keys[2];                             // two random keys used to encode the `thread_delayed_free` list
  mi_random_ctx_t       random;                              // random number context used for secure allocation
  size_t                page_count;                          // total number of pages in the `pages` queues.
  size_t                page_retired_min;                    // smallest retired index (retired pages are fully free, but still in the page queues)
  size_t                page_retired_max;                    // largest retired index into the `pages` array.
  mi_heap_t*            next;                                // list of heaps per thread
  bool                  no_reclaim;                          // `true` if this heap should not reclaim abandoned pages
};



// ------------------------------------------------------
// Debug
// ------------------------------------------------------

#if !defined(MI_DEBUG_UNINIT)
#define MI_DEBUG_UNINIT     (0xD0)
#endif
#if !defined(MI_DEBUG_FREED)
#define MI_DEBUG_FREED      (0xDF)
#endif
#if !defined(MI_DEBUG_PADDING)
#define MI_DEBUG_PADDING    (0xDE)
#endif

#if (MI_DEBUG)
// use our own assertion to print without memory allocation
void _mi_assert_fail(const char* assertion, const char* fname, unsigned int line, const char* func );
#define mi_assert(expr)     ((expr) ? (void)0 : _mi_assert_fail(#expr,__FILE__,__LINE__,__func__))
#else
#define mi_assert(x)
#endif

#if (MI_DEBUG>1)
#define mi_assert_internal    mi_assert
#else
#define mi_assert_internal(x)
#endif

#if (MI_DEBUG>2)
#define mi_assert_expensive   mi_assert
#else
#define mi_assert_expensive(x)
#endif

// ------------------------------------------------------
// Statistics
// ------------------------------------------------------

#ifndef MI_STAT
#if (MI_DEBUG>0)
#define MI_STAT 2
#else
#define MI_STAT 0
#endif
#endif

typedef struct mi_stat_count_s {
  int64_t allocated;
  int64_t freed;
  int64_t peak;
  int64_t current;
} mi_stat_count_t;

typedef struct mi_stat_counter_s {
  int64_t total;
  int64_t count;
} mi_stat_counter_t;

typedef struct mi_stats_s {
  mi_stat_count_t segments;
  mi_stat_count_t pages;
  mi_stat_count_t reserved;
  mi_stat_count_t committed;
  mi_stat_count_t reset;
  mi_stat_count_t page_committed;
  mi_stat_count_t segments_abandoned;
  mi_stat_count_t pages_abandoned;
  mi_stat_count_t threads;
  mi_stat_count_t normal;
  mi_stat_count_t huge;
  mi_stat_count_t large;
  mi_stat_count_t malloc;
  mi_stat_count_t segments_cache;
  mi_stat_counter_t pages_extended;
  mi_stat_counter_t mmap_calls;
  mi_stat_counter_t commit_calls;
  mi_stat_counter_t page_no_retire;
  mi_stat_counter_t searches;
  mi_stat_counter_t normal_count;
  mi_stat_counter_t huge_count;
  mi_stat_counter_t large_count;
#if MI_STAT>1
  mi_stat_count_t normal_bins[MI_BIN_HUGE+1];
#endif
} mi_stats_t;


void _mi_stat_increase(mi_stat_count_t* stat, size_t amount);
void _mi_stat_decrease(mi_stat_count_t* stat, size_t amount);
void _mi_stat_counter_increase(mi_stat_counter_t* stat, size_t amount);

#if (MI_STAT)
#define mi_stat_increase(stat,amount)         _mi_stat_increase( &(stat), amount)
#define mi_stat_decrease(stat,amount)         _mi_stat_decrease( &(stat), amount)
#define mi_stat_counter_increase(stat,amount) _mi_stat_counter_increase( &(stat), amount)
#else
#define mi_stat_increase(stat,amount)         (void)0
#define mi_stat_decrease(stat,amount)         (void)0
#define mi_stat_counter_increase(stat,amount) (void)0
#endif

#define mi_heap_stat_counter_increase(heap,stat,amount)  mi_stat_counter_increase( (heap)->tld->stats.stat, amount)
#define mi_heap_stat_increase(heap,stat,amount)  mi_stat_increase( (heap)->tld->stats.stat, amount)
#define mi_heap_stat_decrease(heap,stat,amount)  mi_stat_decrease( (heap)->tld->stats.stat, amount)

// ------------------------------------------------------
// Thread Local data
// ------------------------------------------------------

// A "span" is is an available range of slices. The span queues keep
// track of slice spans of at most the given `slice_count` (but more than the previous size class).
typedef struct mi_span_queue_s {
  mi_slice_t* first;
  mi_slice_t* last;
  size_t      slice_count;
} mi_span_queue_t;

#define MI_SEGMENT_BIN_MAX (35)     // 35 == mi_segment_bin(MI_SLICES_PER_SEGMENT)

// OS thread local data
typedef struct mi_os_tld_s {
  size_t                region_idx;   // start point for next allocation
  mi_stats_t*           stats;        // points to tld stats
} mi_os_tld_t;


// Segments thread local data
typedef struct mi_segments_tld_s {
  mi_span_queue_t     spans[MI_SEGMENT_BIN_MAX+1];  // free slice spans inside segments
  size_t              count;        // current number of segments;
  size_t              peak_count;   // peak number of segments
  size_t              current_size; // current size of all segments
  size_t              peak_size;    // peak size of all segments
  mi_stats_t*         stats;        // points to tld stats
  mi_os_tld_t*        os;           // points to os stats
} mi_segments_tld_t;

// Thread local data
struct mi_tld_s {
  unsigned long long  heartbeat;     // monotonic heartbeat count
  bool                recurse;       // true if deferred was called; used to prevent infinite recursion.
  mi_heap_t*          heap_backing;  // backing heap of this thread (cannot be deleted)
  mi_heap_t*          heaps;         // list of heaps in this thread (so we can abandon all when the thread terminates)
  mi_segments_tld_t   segments;      // segment tld
  mi_os_tld_t         os;            // os tld
  mi_stats_t          stats;         // statistics
};

#endif
