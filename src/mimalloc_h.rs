/* ----------------------------------------------------------------------------
Copyright (c) 2018-2022, Microsoft Research, Daan Leijen
This is free software; you can redistribute it and/or modify it under the
terms of the MIT license. A copy of the license can be found in the file
"LICENSE" at the root of this distribution.
-----------------------------------------------------------------------------*/
use std::mem::size_of;
use crate::memory::Address;

const MI_MALLOC_VERSION: u16 = 209;   // major + 2 digits minor

pub(crate) const MI_SMALL_WSIZE_MAX: u64 = 128;
pub(crate) const MI_SMALL_SIZE_MAX: u64 = MI_SMALL_WSIZE_MAX * size_of::<u64>() as u64;

// ------------------------------------------------------
// Internals
// ------------------------------------------------------

// typedef void (mi_cdecl mi_deferred_free_fun)(bool force, unsigned long long heartbeat, void* arg);
// mi_decl_export void mi_register_deferred_free(mi_deferred_free_fun* deferred_free, void* arg) mi_attr_noexcept;

// typedef void (mi_cdecl mi_output_fun)(const char* msg, void* arg);
// mi_decl_export void mi_register_output(mi_output_fun* out, void* arg) mi_attr_noexcept;

// typedef void (mi_cdecl mi_error_fun)(int err, void* arg);
// mi_decl_export void mi_register_error(mi_error_fun* fun, void* arg);

// -------------------------------------------------------------------------------------
// Heaps: first-class, but can only allocate from the same thread that created it.
// -------------------------------------------------------------------------------------

struct mi_heap_t {}

// An area of heap space contains blocks of a single size.
struct mi_heap_area_t {
  blocks: Address,  // start of the area containing heap blocks
  reserved: u64,    // bytes reserved for this area (virtual)
  committed: u64,   // current available bytes for this area
  used: u64,        // number of allocated blocks
  block_size: u64,  // size in bytes of each block
  full_block_size: u64, // size in bytes of a full block including padding and metadata.
}

// typedef bool (mi_cdecl mi_block_visit_fun)(const mi_heap_t* heap, const mi_heap_area_t* area, void* block, size_t block_size, void* arg);
// mi_decl_export bool mi_heap_visit_blocks(const mi_heap_t* heap, bool visit_all_blocks, mi_block_visit_fun* visitor, void* arg);

// Experimental: heaps associated with specific memory arena's
// typedef int mi_arena_id_t;

// ------------------------------------------------------
// Convenience
// ------------------------------------------------------

// #define mi_malloc_tp(tp)                ((tp*)mi_malloc(sizeof(tp)))
// #define mi_zalloc_tp(tp)                ((tp*)mi_zalloc(sizeof(tp)))
// #define mi_calloc_tp(tp,n)              ((tp*)mi_calloc(n,sizeof(tp)))
// #define mi_mallocn_tp(tp,n)             ((tp*)mi_mallocn(n,sizeof(tp)))
// #define mi_reallocn_tp(p,tp,n)          ((tp*)mi_reallocn(p,n,sizeof(tp)))
// #define mi_recalloc_tp(p,tp,n)          ((tp*)mi_recalloc(p,n,sizeof(tp)))
//
// #define mi_heap_malloc_tp(hp,tp)        ((tp*)mi_heap_malloc(hp,sizeof(tp)))
// #define mi_heap_zalloc_tp(hp,tp)        ((tp*)mi_heap_zalloc(hp,sizeof(tp)))
// #define mi_heap_calloc_tp(hp,tp,n)      ((tp*)mi_heap_calloc(hp,n,sizeof(tp)))
// #define mi_heap_mallocn_tp(hp,tp,n)     ((tp*)mi_heap_mallocn(hp,n,sizeof(tp)))
// #define mi_heap_reallocn_tp(hp,p,tp,n)  ((tp*)mi_heap_reallocn(hp,p,n,sizeof(tp)))
// #define mi_heap_recalloc_tp(hp,p,tp,n)  ((tp*)mi_heap_recalloc(hp,p,n,sizeof(tp)))


// ------------------------------------------------------
// Options
// ------------------------------------------------------

// TODO
enum mi_option_t {
  // stable options
  mi_option_show_errors,
  mi_option_show_stats,
  mi_option_verbose,
  // some of the following options are experimental
  // (deprecated options are kept for binary backward compatibility with v1.x versions)
  mi_option_eager_commit,
  mi_option_deprecated_eager_region_commit,
  mi_option_deprecated_reset_decommits,
  mi_option_large_os_pages,           // use large (2MiB) OS pages, implies eager commit
  mi_option_reserve_huge_os_pages,    // reserve N huge OS pages (1GiB) at startup
  mi_option_reserve_huge_os_pages_at, // reserve huge OS pages at a specific NUMA node
  mi_option_reserve_os_memory,        // reserve specified amount of OS memory at startup
  mi_option_deprecated_segment_cache,
  mi_option_page_reset,
  mi_option_abandoned_page_decommit,
  mi_option_deprecated_segment_reset,
  mi_option_eager_commit_delay,
  mi_option_decommit_delay,
  mi_option_use_numa_nodes,           // 0 = use available numa nodes, otherwise use at most N nodes.
  mi_option_limit_os_alloc,           // 1 = do not use OS memory for allocation (but only reserved arenas)
  mi_option_os_tag,
  mi_option_max_errors,
  mi_option_max_warnings,
  mi_option_max_segment_reclaim,
  mi_option_allow_decommit,
  mi_option_segment_decommit_delay,  
  mi_option_decommit_extend_delay,
  mi_option_destroy_on_exit,          
  _mi_option_last
}
