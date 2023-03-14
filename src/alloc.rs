/* ----------------------------------------------------------------------------
Copyright (c) 2018-2022, Microsoft Research, Daan Leijen
This is free software; you can redistribute it and/or modify it under the
terms of the MIT license. A copy of the license can be found in the file
"LICENSE" at the root of this distribution.
-----------------------------------------------------------------------------*/

// ------------------------------------------------------
// Allocation
// ------------------------------------------------------

use std::fmt::Pointer;
use std::mem::size_of;

// Fast allocation in a page: just pop from the free list.
// Fall back to generic allocation only if the list is empty.
#[inline]
pub fn _mi_page_malloc(heap: Pointer<mi_heap_t>, page: Pointer<mi_page_t>, size: u64, zero: bool) -> Address {
  mi_assert_internal!(return_field!(page=>xblock_size)==0 || mi_page_block_size(page) >= size);
  let block = return_field!(page=>free);
  if mi_unlikely(block == null) {
    return _mi_malloc_generic(heap, size, zero, 0);
  }
  mi_assert_internal!(block != null && _mi_ptr_page(block) == page);
  // pop from the free list
  update_field!(page=>used, |x| x+1);
  let free = mi_block_next(page, block);
  write_field!(page=>free, free);
  mi_assert_internal(free == null || _mi_ptr_page(free) == page);

  // allow use of the block internally
  // note: when tracking we need to avoid ever touching the MI_PADDING since
  // that is tracked by valgrind etc. as non-accessible (through the red-zone, see `mimalloc-track.h`)
  mi_track_mem_undefined(block, mi_page_usable_block_size(page));

  // zero the block? note: we need to zero the full block size (issue #63)
  if mi_unlikely(zero) {
    mi_assert_internal!(return_field!(page=>xblock_size) != 0); // do not call with zero'ing for huge blocks (see _mi_malloc_generic)
    let zsize: u64 = if return_field!(page=>is_zero) {
      size_of::<mi_block_t::mi_encoded_t>() + MI_PADDING_SIZE
    } else {
      return_field!(page=>xblock_size)
    };
    _mi_memzero_aligned(block, zsize - MI_PADDING_SIZE);
  }
  // TODO: Can we use the previous `return_field!(page=>is_zero)` result?
  #[cfg(all(mi_debug, not(mi_track_enabled)))]
  if !return_field!(page=>is_zero) && !zero && !mi_page_is_huge(page) {
    for i in .. mi_page_usable_block_size(page) {
      memory.write_value(block.offset(i), MI_DEBUG_UNINIT); // TODO: inefficient?
    }
  }
  #[cfg(mi_secure)]
  if !zero { write_field!(block=>next, null); } // don't leak internal data

  #[cfg(mi_stat)]
  {
    let bsize: u64 = mi_page_usable_block_size(page);
    if bsize <= MI_MEDIUM_OBJ_SIZE_MAX {
      mi_heap_stat_increase(heap, normal, bsize);
      mi_heap_stat_counter_increase(heap, normal_count, 1);
      #[cfg(mi_stat_2)]
      {
        let bin: u64 = _mi_bin(bsize);
        mi_heap_stat_increase(heap, normal_bins[bin], 1);
      }
    }
  }

  #[cfg(all(mi_padding, mi_encode_freelist, not(mi_track_enabled)))]
  {
    let padding = Pointer::<mi_padding_t>::from_address(block.byte_address().0 + mi_page_usable_block_size(page));
    let delta: i64 = padding.byte_address().0 - block.byte_address().0 - (size - MI_PADDING_SIZE);
    #[cfg(mi_debug_2)]
    {
      mi_assert_internal!(delta >= 0 && mi_page_usable_block_size(page) >= (size - MI_PADDING_SIZE + delta));
      mi_track_mem_defined(padding, mi_padding_t::size_of());  // note: re-enable since mi_page_usable_block_size may set noaccess
    }
    write_value!(padding=>canary, mi_ptr_encode(page, block, return_value!(page=>keys)) as u32);
    write_value!(padding=>delta, delta as u32);
    if !mi_page_is_huge(page) {
      let fill: Address = padding.byte_address().0 as i64 - delta;
      let maxpad: u64 = min(delta, MI_MAX_ALIGN_SIZE); // set at most N initial padding bytes
      for i in 0 .. maxpad {
        memory.write(fill.offset(i), &[MI_DEBUG_PADDING]); // TODO: may be slow
      }
    }
  }

  block
}

#[inline]
fn mi_heap_malloc_small_zero(heap: Pointer<mi_heap_t>, size: u64, zero: bool) -> Address {
  mi_assert!(heap != null);
  #[cfg(mi_debug)]
  {
    let tid: u64 = _mi_thread_id();
    let our_tid = return_value!(heap=>thread_id);
    mi_assert(our_tid == 0 || our_tid == tid); // heaps are thread local
  }
  mi_assert!(size <= MI_SMALL_SIZE_MAX);
  #[cfg(mi_padding)]
  if size == 0 {
    size = u64::size_of();
  }
  let page: Pointer<mi_page_t> = _mi_heap_get_free_small_page(heap, size + MI_PADDING_SIZE);
  let p: Address = _mi_page_malloc(heap, page, size + MI_PADDING_SIZE, zero);
  mi_assert_internal!(p == null || mi_usable_size(p) >= size);
  #[cfg(mi_stat_2)]
  if p != null {
    if !mi_heap_is_initialized(heap) {
      heap = mi_get_default_heap();
    }
    mi_heap_stat_increase(heap, malloc, mi_usable_size(p));
  }
  mi_track_malloc(p, size, zero);
  p
}

// allocate a small block
#[inline]
fn mi_heap_malloc_small(heap: Pointer<mi_heap_t>, size: u64) -> Address {
  mi_heap_malloc_small_zero(heap, size, false)
}

#[inline]
fn mi_malloc_small(size: u64) -> Address {
  mi_heap_malloc_small(mi_get_default_heap(), size)
}

// The main allocation function
#[inline]
fn _mi_heap_malloc_zero_ex(heap: Pointer<mi_heap_t>, size: u64, zero: bool, huge_alignment: u64) -> Address {
  if mi_likely(size <= MI_SMALL_SIZE_MAX) {
    mi_assert_internal!(huge_alignment == 0);
    return mi_heap_malloc_small_zero(heap, size, zero);
  } else {
    mi_assert!(heap!=null);
    let thread_id = return_value!(heap=>thread_id);
    mi_assert(thread_id == 0 || thread_id == _mi_thread_id());   // heaps are thread local
    let p: Address = _mi_malloc_generic(heap, size + MI_PADDING_SIZE, zero, huge_alignment);  // note: size can overflow but it is detected in malloc_generic
    mi_assert_internal!(p == null || mi_usable_size(p) >= size);
    #[cfg(mi_stat_2)]
    if p != null {
      if !mi_heap_is_initialized(heap) {
        heap = mi_get_default_heap();
      }
      mi_heap_stat_increase(heap, malloc, mi_usable_size(p));
    }
    mi_track_malloc(p, size, zero);
    p
  }
}

#[inline]
fn _mi_heap_malloc_zero(heap: Pointer<mi_heap_t>, size: u64, zero: bool) -> Address {
  _mi_heap_malloc_zero_ex(heap, size, zero, 0)
}

#[inline]
fn mi_heap_malloc(heap: Pointer<mi_heap_t>, size: u64) -> Address {
  _mi_heap_malloc_zero(heap, size, false)
}

#[inline]
fn mi_malloc(size: u64) -> Address {
  mi_heap_malloc(mi_get_default_heap(), size)
}

// zero initialized small block
fn mi_zalloc_small(size: u64) -> Address {
  mi_heap_malloc_small_zero(mi_get_default_heap(), size, true)
}

#[inline]
fn mi_heap_zalloc(heap: ZTypedAddress<mi_heap_t>, size: u64) -> Address {
  return _mi_heap_malloc_zero(heap, size, true);
}

fn mi_zalloc(size: u64) -> Address {
  return mi_heap_zalloc(mi_get_default_heap(), size);
}


// ------------------------------------------------------
// Check for double free in secure and debug mode
// This is somewhat expensive so only enabled for secure mode 4
// ------------------------------------------------------

// linear check if the free list contains a specific element
#[cfg(all(mi_encode_freelist, any(mi_secure_5, mi_debug)))]
fn mi_list_contains(page: Pointer<mi_page_t>, list: Pointer<mi_block_t>, elem: Pointer<mi_block_t>) -> bool {
  while list != null {
    if elem==list {
      return true;
    }
    list = mi_block_next(page, list);
  }
  false
}

#[cfg(all(mi_encode_freelist, any(mi_secure_5, mi_debug)))]
fn mi_check_is_double_freex(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) -> bool {
  // The decoded value is in the same page (or NULL).
  // Walk the free lists to verify positively if it is already freed
  if mi_list_contains(page, return_value!(page=>free), block) ||
      mi_list_contains(page, return_value!(page=>local_free), block) ||
      mi_list_contains(page, mi_page_thread_free(page), block)
  {
    _mi_error_message(EAGAIN, "double free detected of block %p with size %zu\n", block, mi_page_block_size(page));
    return true;
  }
  false
}

#[cfg(all(mi_encode_freelist, any(mi_secure_5, mi_debug)))]
// #[macro_export] // FIXME: needed?
macro_rules! mi_track_page {
  ($page:expr,$access:ident) => {
    {
      let mut psize: u64;
      let pstart: Address = _mi_page_start(_mi_page_segment(page), page, &psize);
      concat_idents!(mi_track_mem_, access)(pstart, psize);
    }
  }
}

#[cfg(all(mi_encode_freelist, any(mi_secure_5, mi_debug)))]
#[inline]
fn mi_check_is_double_free(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) -> bool {
  let mut is_double_free = false;
  let n: Pointer<mi_block_t> =  = mi_block_nextx(page, block, return_value!(page=>keys)); // pretend it is freed, and get the decoded first field
  if ((n as u64 & (MI_INTPTR_SIZE-1)) == 0 &&  // quick check: aligned pointer?
      (n==null || mi_is_in_same_page(block, n))) // quick check: in same page or NULL?
  {
    // Suspicous: decoded value a in block is in the same page (or NULL) -- maybe a double free?
    // (continue in separate function to improve code generation)
    is_double_free = mi_check_is_double_freex(page, block);
  }
  is_double_free
}

#[cfg(not(all(mi_encode_freelist, any(mi_secure_5, mi_debug))))]
#[inline]
fn mi_check_is_double_free(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) -> bool {
  MI_UNUSED(page);
  MI_UNUSED(block);
  false
}

// ---------------------------------------------------------------------------
// Check for heap block overflow by setting up padding at the end of the block
// ---------------------------------------------------------------------------

#[cfg(all(mi_padding, mi_encode_freelist, not(mi_track_enabled)))]
fn mi_page_decode_padding(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>, delta: &mut u64, bsize: &mut u64) -> bool {
  *bsize = mi_page_usable_block_size(page);
  let padding: Pointer<mi_padding_t> = Pointer::from_address(block.byte_address() + *bsize);
  mi_track_mem_defined(padding, mi_padding_t::size_of());
  *delta = return_value!(padding=>delta);
  let canary: u32 = return_value!(padding=>canary);
  let keys: [u64; 2] = return_value!(page=>keys);
  let ok = mi_ptr_encode(page, block, &keys).byte_address() == canary && *delta <= *bsize;
  mi_track_mem_noaccess(padding, mi_padding_t::size_of());
  ok
}

// Return the exact usable size of a block.
#[cfg(all(mi_padding, mi_encode_freelist, not(mi_track_enabled)))]
fn mi_page_usable_size_of(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) -> u64 {
  let mut bsize: u64;
  let mut delta: u64;
  let ok = mi_page_decode_padding(page, block, &mut delta, &mut bsize);
  mi_assert_internal!(ok);
  mi_assert_internal!(delta <= bsize);
  if ok {
    bsize - delta
  } else {
    0
  }
}

#[cfg(all(mi_padding, mi_encode_freelist, not(mi_track_enabled)))]
fn mi_verify_padding(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>, size: &mut u64, wrong: &mut u64) -> bool {
  let mut bsize: u64;
  let mut delta: u64;
  let ok: bool = mi_page_decode_padding(page, block, &mut delta, &mut bsize);
  *size = *wrong = bsize;
  if !ok {
    return false;
  }
  mi_assert_internal!(bsize >= delta);
  *size = bsize - delta;
  if !mi_page_is_huge(page) {
    let fill: u64 = block.byte_address() + bsize - delta;
    let maxpad: u64 = min(delta, MI_MAX_ALIGN_SIZE); // check at most the first N padding bytes
    mi_track_mem_defined(fill, maxpad);
    for i in 0 .. maxpad {
      if fill[i] != MI_DEBUG_PADDING {
        *wrong = bsize - delta + i;
        ok = false;
        break;
      }
    }
    mi_track_mem_noaccess(fill, maxpad);
  }
  ok
}

#[cfg(all(mi_padding, mi_encode_freelist, not(mi_track_enabled)))]
fn mi_check_padding(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) {
  u64 size;
  u64 wrong;
  if !mi_verify_padding(page, block, &mut size, &mut wrong) {
    _mi_error_message!(EFAULT, "buffer overflow in heap block %p of size %zu: write after %zu bytes\n", block, size, wrong);
  }
}

// When a non-thread-local block is freed, it becomes part of the thread delayed free
// list that is freed later by the owning heap. If the exact usable size is too small to
// contain the pointer for the delayed list, then shrink the padding (by decreasing delta)
// so it will later not trigger an overflow error in `mi_free_block`.
#[cfg(all(mi_padding, mi_encode_freelist, not(mi_track_enabled)))]
fn mi_padding_shrink(page: Pointer<mi_page_t>, block Pointer<mi_block_t>, min_size: u64) {
  let mut bsize: u64;
  let mut delta: u64;
  let ok = mi_page_decode_padding(page, block, &mut delta, &mut bsize);
  mi_assert_internal!(ok);
  if !ok || (bsize - delta) >= min_size { // usually already enough space
    return;
  }
  mi_assert_internal!(bsize >= min_size);
  if bsize < min_size { // should never happen // TODO: Add assert.
    return;
  };
  let new_delta: u64 = bsize - min_size;
  mi_assert_internal!(new_delta < bsize);
  let padding = Pointer::<mi_padding_t>::from_address(block.byte_address() + bsize);
  write_value!(padding=>delta, new_delta as u32);
}

#[cfg(not(all(mi_padding, mi_encode_freelist, not(mi_track_enabled))))]
fn mi_check_padding(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) {
  MI_UNUSED!(page);
  MI_UNUSED!(block);
}

#[cfg(not(all(mi_padding, mi_encode_freelist, not(mi_track_enabled))))]
fn mi_page_usable_size_of(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) -> u64 {
  MI_UNUSED!(block);
  mi_page_usable_block_size(page)
}

#[cfg(not(all(mi_padding, mi_encode_freelist, not(mi_track_enabled))))]
fn mi_padding_shrink(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>, min_size: u64) {
  MI_UNUSED!(page);
  MI_UNUSED!(block);
  MI_UNUSED!(min_size);
}

// only maintain stats for smaller objects if requested
#[cfg(mi_stat)]
fn mi_stat_free(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) {
  #[cfg(not(mi_stat_2)] // FIXME: Check applying to macro as block.
  MI_UNUSED!(block);
  let heap: Pointer<mi_heap_t> = mi_heap_get_default();
  let bsize: u64 = mi_page_usable_block_size(page);
  #[cfg(mi_stat_2)]
  {
    let usize: u64 = mi_page_usable_size_of(page, block);
    mi_heap_stat_decrease(heap, malloc, usize);
  }
  if bsize <= MI_MEDIUM_OBJ_SIZE_MAX {
    mi_heap_stat_decrease(heap, normal, bsize);
    #[cfg(mi_stat_2)]
    mi_heap_stat_decrease(heap, normal_bins[_mi_bin(bsize)], 1);
  } else if bsize <= MI_LARGE_OBJ_SIZE_MAX {
    mi_heap_stat_decrease(heap, large, bsize);
  } else {
    mi_heap_stat_decrease(heap, huge, bsize);
  }
}

#[cfg(not(mi_stat))]
fn mi_stat_free(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>) {
  MI_UNUSED!(page);
  MI_UNUSED!(block);
}

#if MI_HUGE_PAGE_ABANDON
#if (MI_STAT>0)

// maintain stats for huge objects
#[cfg(all(mi_huge_page_abandon, mi_stat))]
fn mi_stat_huge_free(page: Pointer<mi_page_t>) {
  let heap: Pointer<mi_heap_t> = mi_heap_get_default();
  let bsize: u64 = mi_page_block_size(page); // to match stats in `page.c:mi_page_huge_alloc`
  if bsize <= MI_LARGE_OBJ_SIZE_MAX {
    mi_heap_stat_decrease(heap, large, bsize);
  } else {
    mi_heap_stat_decrease(heap, huge, bsize);
  }
}

#[cfg(all(mi_huge_page_abandon, not(mi_stat))]
fn mi_stat_huge_free(page: Pointer<mi_page_t>) {
  MI_UNUSED!(page);
}

// ------------------------------------------------------
// Free
// ------------------------------------------------------

// multi-threaded free (or free in huge block if compiled with MI_HUGE_PAGE_ABANDON)
fn _mi_free_block_mt(page: Pointer<mi_page_t>, block: Pointer<mi_block_t>)
{
  // The padding check may access the non-thread-owned page for the key values.
  // that is safe as these are constant and the page won't be freed (as the block is not freed yet).
  mi_check_padding(page, block);
  mi_padding_shrink(page, block, sizeof(mi_block_t));       // for small size, ensure we can fit the delayed thread pointers without triggering overflow detection

  // huge page segments are always abandoned and can be freed immediately
  let segment: Pointer<mi_segment_t> = _mi_page_segment(page);
  if return_value!(segment=>kind) == MI_SEGMENT_HUGE {
    #[cfg(mi_huge_page_abandon)]
    {
      // huge page segments are always abandoned and can be freed immediately
      mi_stat_huge_free(page);
      _mi_segment_huge_page_free(segment, page, block);
      return;
    }
    // huge pages are special as they occupy the entire segment
    // as these are large we reset the memory occupied by the page so it is available to other threads
    // (as the owning thread needs to actually free the memory later).
    #[cfg(not(mi_huge_page_abandon))]
    _mi_segment_huge_page_reset(segment, page, block);
  }

  // note: when tracking, cannot use mi_usable_size with multi-threading
  #[cfg(all(mi_debug, not(mi_track_enabled)))]
  if return_value!(segment=>kind) != MI_SEGMENT_HUGE {                   // not for huge segments as we just reset the content
    memset(block, MI_DEBUG_FREED, mi_usable_size(block));
    for i in .. mi_usable_size(block) {
      memory.write(block.byte_address() + i, &[MI_DEBUG_FREED]);
    }
  }

  // Try to put the block on either the page-local thread free list, or the heap delayed free list.
  let mut tfreex: mi_thread_free_t;
  let mut use_delayed: bool;
  let tfree: mi_thread_free_t = mi_atomic_load_relaxed(&return_value!(page=>xthread_free));
  loop {
    use_delayed = mi_tf_delayed(tfree) == MI_USE_DELAYED_FREE;
    if mi_unlikely(use_delayed) {
      // unlikely: this only happens on the first concurrent free in a page that is in the full list
      tfreex = mi_tf_set_delayed(tfree, MI_DELAYED_FREEING);
    } else {
      // usual: directly add to page thread_free list
      mi_block_set_next(page, block, mi_tf_block(tfree));
      tfreex = mi_tf_set_block(tfree, block);
    }
    // TODO: Can we use the previous value of `return_value!(page=>xthread_free)`?
    if mi_atomic_cas_weak_release(&return_value!(page=>xthread_free), &mut tfree, tfreex) {
      break;
    }
  }

  if mi_unlikely(use_delayed) {
    // racy read on `heap`, but ok because MI_DELAYED_FREEING is set (see `mi_heap_delete` and `mi_heap_collect_abandon`)
    let heap: Pointer<mi_heap_t> = Pointer::from_address(mi_atomic_load_acquire(&return_value!(page=>xheap))); //mi_page_heap(page);
    mi_assert_internal!(heap != NULL);
    if heap != null {
      // add to the delayed free list of this heap. (do this atomically as the lock only protects heap memory validity)
      let dfree: Pointer<mi_block_t> = mi_atomic_load_ptr_relaxed(mi_block_t, &return_value!(page=>thread_delayed_free));
      loop {
        mi_block_set_nextx(heap, block, dfree, return_value!(heap=>keys));
        if mi_atomic_cas_ptr_weak_release(mi_block_t, &return_value!(heap=>thread_delayed_free), &dfree, block) {
          break;
        }
      }
    }

    // and reset the MI_DELAYED_FREEING flag
    // TODO: Can we use the previous value of `return_value!(page=>xthread_free)`?
    tfree = mi_atomic_load_relaxed(&return_value!(page=>xthread_free));
    loop {
      tfreex = tfree;
      mi_assert_internal!(mi_tf_delayed(tfree) == MI_DELAYED_FREEING);
      tfreex = mi_tf_set_delayed(tfree, MI_NO_DELAYED_FREE);
      // TODO: Can we use the previous value of `return_value!(page=>xthread_free)`?
      if mi_atomic_cas_weak_release(&return_value!(page=>xthread_free), &tfree, tfreex) {
        break;
      }
    }
  }
}

// regular free
#[inline]
fn _mi_free_block(page: Pointer<mi_page_t>, local: bool, block: Pointer<mi_block_t>) {
  // and push it on the free list
  //const size_t bsize = mi_page_block_size(page);
  if mi_likely(local) {
    // owning thread can free a block directly
    if mi_unlikely(mi_check_is_double_free(page, block)) {
      return;
    }
    mi_check_padding(page, block);
    #[cfg(all(mi_debug, mi_track_enabled))]
    if !mi_page_is_huge(page) {   // huge page content may be already decommitted
      // TODO: possibly inefficient
      for i in .. mi_page_block_size(page) {
        memory.write(block.byte_address().offset(i), &[MI_DEBUG_FREED]);
      }
    }
    mi_block_set_next(page, block, read_value!(page=>local_free));
    write_value!(page=>local_free, block);
    update_value!(page=>used, |x| x - 1);
    if mi_unlikely(mi_page_all_free(page)) {
      _mi_page_retire(page);
    } else if mi_unlikely(mi_page_is_in_full(page)) {
      _mi_page_unfull(page);
    }
  } else {
    _mi_free_block_mt(page,block);
  }
}

// Adjust a block that was allocated aligned, to the actual start of the block in the page.
fn _mi_page_ptr_unalign(segment: Pointer<mi_segment_t>, page: Pointer<mi_page_t>, p: u64) -> Pointer<mi_block_t> {
  mi_assert_internal!(page!=null && p!=null);
  let diff  : u64 = p - _mi_page_start(segment, page, null);
  let adjust: u64 = diff % mi_page_block_size(page);
  return Pointer::from_address(p - adjust);
}

fn _mi_free_generic(segment: Pointer<mi_segment_t>, page: Pointer<mi_page_t>, is_local: bool, p: u64) {
  let block: Pointer<mi_block_t> = if mi_page_has_aligned(page) {
    _mi_page_ptr_unalign(segment, page, p)
  } else {
    Pointer::from_address(p);
  };
  mi_stat_free(page, block);                 // stat_free may access the padding
  mi_track_free(p);
  _mi_free_block(page, is_local, block);
}

// Get the segment data belonging to a pointer
// This is just a single `and` in assembly but does further checks in debug mode
// (and secure mode) if this was a valid pointer.
#[inline]
fn mi_checked_ptr_segment(p: u64, msg: &str) -> Pointer<mi_segment_t>
{
  MI_UNUSED!(msg);
  mi_assert!(p != null);

  #[cfg(mi_debug)]
  if mi_unlikely((p & (MI_INTPTR_SIZE - 1)) != 0) {
    _mi_error_message(EINVAL, "%s: invalid (unaligned) pointer: %p\n", msg, p);
    return Pointer::from_address(null);
  }

  let segment: Pointer<mi_segment_t> = _mi_ptr_segment(p);
  mi_assert_internal!(segment != null);

  let cookie = return_value!(segment=>cookie);
  #[cfg(mi_debug)]
  if mi_unlikely(!mi_is_in_heap_region(p)) {
    if !(MI_INTPTR_SIZE == 8 && std::env::consts::OS == "linux") || // TODO: Use `os_type` crate instead?
        (p >> 40) != 0x7F // linux tends to align large blocks above 0x7F000000000 (issue #640)
    {
        _mi_warning_message!("%s: pointer might not point to a valid heap region: %p\n"
        "(this may still be a valid very large allocation (over 64MiB))\n", msg, p);
        if mi_likely(_mi_ptr_cookie(segment) == cookie) {
          _mi_warning_message!("(yes, the previous pointer %p was valid after all)\n", p);
        }
    }
  }
  #[cfg(any(mi_debug, mi_secure_5))]
  if mi_unlikely(_mi_ptr_cookie(segment) != cookie) {
    _mi_error_message(EINVAL, "%s: pointer does not point to a valid heap space: %p\n", msg, p);
    return null;
  }

  return segment;
}

// Free a block
// fast path written carefully to prevent spilling on the stack
fn mi_free(p: Address) {
  if mi_unlikely(p == NULL) {
    return;
  }
  let segment: Pointer<mi_segment_t> = mi_checked_ptr_segment(p,"mi_free");
  let is_local= _mi_thread_id() == mi_atomic_load_relaxed(&read_value!(segment=>thread_id));
  let page: Pointer<mi_page_t> = _mi_segment_page_of(segment, p);

  if mi_likely(is_local) {                       // thread-local free?
    if mi_likely(return_value!(page=>flags).full_aligned == 0)  // and it is not a full page (full pages need to move from the full bin), nor has aligned blocks (aligned blocks need to be unaligned)
    {
      let block: Pointer<mi_block_t> = Pointer::from_address(p);
      if mi_unlikely(mi_check_is_double_free(page, block)) {
        return;
      }
      mi_check_padding(page, block);
      mi_stat_free(page, block);
      #[cfg(all(mi_debug, not(mi_track_enabled)))]
      for i in .. mi_page_block_size(page) { // TODO: possibly slow
        write_value!(block.byte_address() + i, MI_DEBUG_FREED);
      }
      mi_track_free(p);
      mi_block_set_next(page, block, return_value!(page=>local_free));
      write_value!(page=>local_free, block);
      let used = return_value!(page=>used);
      --used;
      write_value!(page=>used, used);
      if mi_unlikely(used == 0) {   // using this expression generates better code than: page->used--; if (mi_page_all_free(page))
        _mi_page_retire(page);
      }
    } else {
      // page is full or contains (inner) aligned blocks; use generic path
      _mi_free_generic(segment, page, true, p);
    }
  }
  else {
    // not thread-local; use generic path
    _mi_free_generic(segment, page, false, p);
  }
}

// return true if successful
fn _mi_free_delayed_block(block: Pointer<mi_block_t>) -> bool {
  // get segment and page
  let segment: Pointer<mi_segment_t> = _mi_ptr_segment(block);
  mi_assert_internal!(_mi_ptr_cookie(segment) == segment->cookie);
  mi_assert_internal!(_mi_thread_id() == segment->thread_id);
  let page: Pointer<mi_page_t> = _mi_segment_page_of(segment, block);

  // Clear the no-delayed flag so delayed freeing is used again for this page.
  // This must be done before collecting the free lists on this page -- otherwise
  // some blocks may end up in the page `thread_free` list with no blocks in the
  // heap `thread_delayed_free` list which may cause the page to be never freed!
  // (it would only be freed if we happen to scan it in `mi_page_queue_find_free_ex`)
  if !_mi_page_try_use_delayed_free(page, MI_USE_DELAYED_FREE, false /* dont overwrite never delayed */) {
    return false;
  }

  // collect all other non-local frees to ensure up-to-date `used` count
  _mi_page_free_collect(page, false);

  // and free the block (possibly freeing the page as well since used is updated)
  _mi_free_block(page, true, block);
  true
}

// Bytes available in a block
fn mi_page_usable_aligned_size_of(segment: Pointer<mi_segment_t>, page: Pointer<mi_page_t>, p: Address) -> u64 {
  let block: Pointer<mi_block_t> = _mi_page_ptr_unalign(segment, page, p);
  let size: u64 = mi_page_usable_size_of(page, block);
  let adjust: i64 = p.byte_address() as i64 - block.byte_address() as i64;
  mi_assert_internal!(adjust >= 0 && adjust as u64 <= size);
  size - adjust
}

#[inline]
fn _mi_usable_size(p: Address, msg: &str) -> u64 {
  if p == null {
    return 0;
  }
  let segment: Pointer<mi_segment_t>  = mi_checked_ptr_segment(p, msg);
  let page: Pointer<mi_page_t> = _mi_segment_page_of(segment, p);
  if mi_likely(!mi_page_has_aligned(page)) {
    let block: Pointer<mi_block_t> = Pointer::from_address(p);
    mi_page_usable_size_of(page, block)
  } else {
    // split out to separate routine for improved code generation
    mi_page_usable_aligned_size_of(segment, page, p)
  }
}

fn mi_usable_size(p: Address) -> u64 {
  _mi_usable_size(p, "mi_usable_size")
}


// ------------------------------------------------------
// Allocation extensions
// ------------------------------------------------------

///////////////////////////////////////////////////////////////////////////////////////////////

fn mi_free_size(p: Pointer, size: u64) {
  MI_UNUSED_RELEASE!(size);
  mi_assert(p == null || size <= _mi_usable_size(p,"mi_free_size"));
  mi_free(p);
}

void mi_free_size_aligned(void* p, size_t size, size_t alignment) mi_attr_noexcept {
  MI_UNUSED_RELEASE(alignment);
  mi_assert(((uintptr_t)p % alignment) == 0);
  mi_free_size(p,size);
}

void mi_free_aligned(void* p, size_t alignment) mi_attr_noexcept {
  MI_UNUSED_RELEASE(alignment);
  mi_assert(((uintptr_t)p % alignment) == 0);
  mi_free(p);
}

mi_decl_nodiscard extern inline mi_decl_restrict void* mi_heap_calloc(mi_heap_t* heap, size_t count, size_t size) mi_attr_noexcept {
  size_t total;
  if (mi_count_size_overflow(count,size,&total)) return NULL;
  return mi_heap_zalloc(heap,total);
}

mi_decl_nodiscard mi_decl_restrict void* mi_calloc(size_t count, size_t size) mi_attr_noexcept {
  return mi_heap_calloc(mi_get_default_heap(),count,size);
}

// Uninitialized `calloc`
mi_decl_nodiscard extern mi_decl_restrict void* mi_heap_mallocn(mi_heap_t* heap, size_t count, size_t size) mi_attr_noexcept {
  size_t total;
  if (mi_count_size_overflow(count, size, &total)) return NULL;
  return mi_heap_malloc(heap, total);
}

mi_decl_nodiscard mi_decl_restrict void* mi_mallocn(size_t count, size_t size) mi_attr_noexcept {
  return mi_heap_mallocn(mi_get_default_heap(),count,size);
}

// Expand (or shrink) in place (or fail)
void* mi_expand(void* p, size_t newsize) mi_attr_noexcept {
  #if MI_PADDING
  // we do not shrink/expand with padding enabled
  MI_UNUSED(p); MI_UNUSED(newsize);
  return NULL;
  #else
  if (p == NULL) return NULL;
  const size_t size = _mi_usable_size(p,"mi_expand");
  if (newsize > size) return NULL;
  return p; // it fits
  #endif
}

void* _mi_heap_realloc_zero(mi_heap_t* heap, void* p, size_t newsize, bool zero) mi_attr_noexcept {
  // if p == NULL then behave as malloc.
  // else if size == 0 then reallocate to a zero-sized block (and don't return NULL, just as mi_malloc(0)).
  // (this means that returning NULL always indicates an error, and `p` will not have been freed in that case.)
  const size_t size = _mi_usable_size(p,"mi_realloc"); // also works if p == NULL (with size 0)
  if mi_unlikely(newsize <= size && newsize >= (size / 2) && newsize > 0) {  // note: newsize must be > 0 or otherwise we return NULL for realloc(NULL,0)
    // todo: adjust potential padding to reflect the new size?
    mi_track_free_size(p, size);
    mi_track_malloc(p,newsize,true);
    return p;  // reallocation still fits and not more than 50% waste
  }
  void* newp = mi_heap_malloc(heap,newsize);
  if mi_likely(newp != NULL) {
    if (zero && newsize > size) {
      // also set last word in the previous allocation to zero to ensure any padding is zero-initialized
      const size_t start = (size >= sizeof(intptr_t) ? size - sizeof(intptr_t) : 0);
      memset((uint8_t*)newp + start, 0, newsize - start);
    }
    if mi_likely(p != NULL) {
      if mi_likely(_mi_is_aligned(p, sizeof(uintptr_t))) {  // a client may pass in an arbitrary pointer `p`..
        const size_t copysize = (newsize > size ? size : newsize);
        mi_track_mem_defined(p,copysize);  // _mi_useable_size may be too large for byte precise memory tracking..
        _mi_memcpy_aligned(newp, p, copysize);
      }
      mi_free(p); // only free the original pointer if successful
    }
  }
  return newp;
}

mi_decl_nodiscard void* mi_heap_realloc(mi_heap_t* heap, void* p, size_t newsize) mi_attr_noexcept {
  return _mi_heap_realloc_zero(heap, p, newsize, false);
}

mi_decl_nodiscard void* mi_heap_reallocn(mi_heap_t* heap, void* p, size_t count, size_t size) mi_attr_noexcept {
  size_t total;
  if (mi_count_size_overflow(count, size, &total)) return NULL;
  return mi_heap_realloc(heap, p, total);
}


// Reallocate but free `p` on errors
mi_decl_nodiscard void* mi_heap_reallocf(mi_heap_t* heap, void* p, size_t newsize) mi_attr_noexcept {
  void* newp = mi_heap_realloc(heap, p, newsize);
  if (newp==NULL && p!=NULL) mi_free(p);
  return newp;
}

mi_decl_nodiscard void* mi_heap_rezalloc(mi_heap_t* heap, void* p, size_t newsize) mi_attr_noexcept {
  return _mi_heap_realloc_zero(heap, p, newsize, true);
}

mi_decl_nodiscard void* mi_heap_recalloc(mi_heap_t* heap, void* p, size_t count, size_t size) mi_attr_noexcept {
  size_t total;
  if (mi_count_size_overflow(count, size, &total)) return NULL;
  return mi_heap_rezalloc(heap, p, total);
}


mi_decl_nodiscard void* mi_realloc(void* p, size_t newsize) mi_attr_noexcept {
  return mi_heap_realloc(mi_get_default_heap(),p,newsize);
}

mi_decl_nodiscard void* mi_reallocn(void* p, size_t count, size_t size) mi_attr_noexcept {
  return mi_heap_reallocn(mi_get_default_heap(),p,count,size);
}

// Reallocate but free `p` on errors
mi_decl_nodiscard void* mi_reallocf(void* p, size_t newsize) mi_attr_noexcept {
  return mi_heap_reallocf(mi_get_default_heap(),p,newsize);
}

mi_decl_nodiscard void* mi_rezalloc(void* p, size_t newsize) mi_attr_noexcept {
  return mi_heap_rezalloc(mi_get_default_heap(), p, newsize);
}

mi_decl_nodiscard void* mi_recalloc(void* p, size_t count, size_t size) mi_attr_noexcept {
  return mi_heap_recalloc(mi_get_default_heap(), p, count, size);
}



// ------------------------------------------------------
// strdup, strndup, and realpath
// ------------------------------------------------------

// `strdup` using mi_malloc
mi_decl_nodiscard mi_decl_restrict char* mi_heap_strdup(mi_heap_t* heap, const char* s) mi_attr_noexcept {
  if (s == NULL) return NULL;
  size_t n = strlen(s);
  char* t = (char*)mi_heap_malloc(heap,n+1);
  if (t == NULL) return NULL;
  _mi_memcpy(t, s, n);
  t[n] = 0;
  return t;
}

mi_decl_nodiscard mi_decl_restrict char* mi_strdup(const char* s) mi_attr_noexcept {
  return mi_heap_strdup(mi_get_default_heap(), s);
}

// `strndup` using mi_malloc
mi_decl_nodiscard mi_decl_restrict char* mi_heap_strndup(mi_heap_t* heap, const char* s, size_t n) mi_attr_noexcept {
  if (s == NULL) return NULL;
  const char* end = (const char*)memchr(s, 0, n);  // find end of string in the first `n` characters (returns NULL if not found)
  const size_t m = (end != NULL ? (size_t)(end - s) : n);  // `m` is the minimum of `n` or the end-of-string
  mi_assert_internal(m <= n);
  char* t = (char*)mi_heap_malloc(heap, m+1);
  if (t == NULL) return NULL;
  _mi_memcpy(t, s, m);
  t[m] = 0;
  return t;
}

mi_decl_nodiscard mi_decl_restrict char* mi_strndup(const char* s, size_t n) mi_attr_noexcept {
  return mi_heap_strndup(mi_get_default_heap(),s,n);
}

#ifndef __wasi__
// `realpath` using mi_malloc
#ifdef _WIN32
#ifndef PATH_MAX
#define PATH_MAX MAX_PATH
#endif
#include <windows.h>
mi_decl_nodiscard mi_decl_restrict char* mi_heap_realpath(mi_heap_t* heap, const char* fname, char* resolved_name) mi_attr_noexcept {
  // todo: use GetFullPathNameW to allow longer file names
  char buf[PATH_MAX];
  DWORD res = GetFullPathNameA(fname, PATH_MAX, (resolved_name == NULL ? buf : resolved_name), NULL);
  if (res == 0) {
    errno = GetLastError(); return NULL;
  }
  else if (res > PATH_MAX) {
    errno = EINVAL; return NULL;
  }
  else if (resolved_name != NULL) {
    return resolved_name;
  }
  else {
    return mi_heap_strndup(heap, buf, PATH_MAX);
  }
}
#else
/*
#include <unistd.h>  // pathconf
static size_t mi_path_max(void) {
  static size_t path_max = 0;
  if (path_max <= 0) {
    long m = pathconf("/",_PC_PATH_MAX);
    if (m <= 0) path_max = 4096;      // guess
    else if (m < 256) path_max = 256; // at least 256
    else path_max = m;
  }
  return path_max;
}
*/
char* mi_heap_realpath(mi_heap_t* heap, const char* fname, char* resolved_name) mi_attr_noexcept {
  if (resolved_name != NULL) {
    return realpath(fname,resolved_name);
  }
  else {
    char* rname = realpath(fname, NULL);
    if (rname == NULL) return NULL;
    char* result = mi_heap_strdup(heap, rname);
    free(rname);  // use regular free! (which may be redirected to our free but that's ok)
    return result;
  }
  /*
    const size_t n  = mi_path_max();
    char* buf = (char*)mi_malloc(n+1);
    if (buf == NULL) {
      errno = ENOMEM;
      return NULL;
    }
    char* rname  = realpath(fname,buf);
    char* result = mi_heap_strndup(heap,rname,n); // ok if `rname==NULL`
    mi_free(buf);
    return result;
  }
  */
}
#endif

mi_decl_nodiscard mi_decl_restrict char* mi_realpath(const char* fname, char* resolved_name) mi_attr_noexcept {
  return mi_heap_realpath(mi_get_default_heap(),fname,resolved_name);
}
#endif

/*-------------------------------------------------------
C++ new and new_aligned
The standard requires calling into `get_new_handler` and
throwing the bad_alloc exception on failure. If we compile
with a C++ compiler we can implement this precisely. If we
use a C compiler we cannot throw a `bad_alloc` exception
but we call `exit` instead (i.e. not returning).
-------------------------------------------------------*/

#ifdef __cplusplus
#include <new>
static bool mi_try_new_handler(bool nothrow) {
  #if defined(_MSC_VER) || (__cplusplus >= 201103L)
    std::new_handler h = std::get_new_handler();
  #else
    std::new_handler h = std::set_new_handler();
    std::set_new_handler(h);
  #endif
  if (h==NULL) {
    _mi_error_message(ENOMEM, "out of memory in 'new'");
    if (!nothrow) {
      throw std::bad_alloc();
    }
    return false;
  }
  else {
    h();
    return true;
  }
}
#else
typedef void (*std_new_handler_t)(void);

#if (defined(__GNUC__) || (defined(__clang__) && !defined(_MSC_VER)))  // exclude clang-cl, see issue #631
std_new_handler_t __attribute__((weak)) _ZSt15get_new_handlerv(void) {
  return NULL;
}
static std_new_handler_t mi_get_new_handler(void) {
  return _ZSt15get_new_handlerv();
}
#else
// note: on windows we could dynamically link to `?get_new_handler@std@@YAP6AXXZXZ`.
static std_new_handler_t mi_get_new_handler() {
  return NULL;
}
#endif

static bool mi_try_new_handler(bool nothrow) {
  std_new_handler_t h = mi_get_new_handler();
  if (h==NULL) {
    _mi_error_message(ENOMEM, "out of memory in 'new'");
    if (!nothrow) {
      abort();  // cannot throw in plain C, use abort
    }
    return false;
  }
  else {
    h();
    return true;
  }
}
#endif

static mi_decl_noinline void* mi_heap_try_new(mi_heap_t* heap, size_t size, bool nothrow ) {
  void* p = NULL;
  while(p == NULL && mi_try_new_handler(nothrow)) {
    p = mi_heap_malloc(heap,size);
  }
  return p;
}

static mi_decl_noinline void* mi_try_new(size_t size, bool nothrow) {
  return mi_heap_try_new(mi_get_default_heap(), size, nothrow);
}


mi_decl_nodiscard mi_decl_restrict extern inline void* mi_heap_alloc_new(mi_heap_t* heap, size_t size) {
  void* p = mi_heap_malloc(heap,size);
  if mi_unlikely(p == NULL) return mi_heap_try_new(heap, size, false);
  return p;
}

mi_decl_nodiscard mi_decl_restrict void* mi_new(size_t size) {
  return mi_heap_alloc_new(mi_get_default_heap(), size);
}


mi_decl_nodiscard mi_decl_restrict extern inline void* mi_heap_alloc_new_n(mi_heap_t* heap, size_t count, size_t size) {
  size_t total;
  if mi_unlikely(mi_count_size_overflow(count, size, &total)) {
    mi_try_new_handler(false);  // on overflow we invoke the try_new_handler once to potentially throw std::bad_alloc
    return NULL;
  }
  else {
    return mi_heap_alloc_new(heap,total);
  }
}

mi_decl_nodiscard mi_decl_restrict void* mi_new_n(size_t count, size_t size) {
  return mi_heap_alloc_new_n(mi_get_default_heap(), size, count);
}


mi_decl_nodiscard mi_decl_restrict void* mi_new_nothrow(size_t size) mi_attr_noexcept {
  void* p = mi_malloc(size);
  if mi_unlikely(p == NULL) return mi_try_new(size, true);
  return p;
}

mi_decl_nodiscard mi_decl_restrict void* mi_new_aligned(size_t size, size_t alignment) {
  void* p;
  do {
    p = mi_malloc_aligned(size, alignment);
  }
  while(p == NULL && mi_try_new_handler(false));
  return p;
}

mi_decl_nodiscard mi_decl_restrict void* mi_new_aligned_nothrow(size_t size, size_t alignment) mi_attr_noexcept {
  void* p;
  do {
    p = mi_malloc_aligned(size, alignment);
  }
  while(p == NULL && mi_try_new_handler(true));
  return p;
}

mi_decl_nodiscard void* mi_new_realloc(void* p, size_t newsize) {
  void* q;
  do {
    q = mi_realloc(p, newsize);
  } while (q == NULL && mi_try_new_handler(false));
  return q;
}

mi_decl_nodiscard void* mi_new_reallocn(void* p, size_t newcount, size_t size) {
  size_t total;
  if mi_unlikely(mi_count_size_overflow(newcount, size, &total)) {
    mi_try_new_handler(false);  // on overflow we invoke the try_new_handler once to potentially throw std::bad_alloc
    return NULL;
  }
  else {
    return mi_new_realloc(p, total);
  }
}

// ------------------------------------------------------
// ensure explicit external inline definitions are emitted!
// ------------------------------------------------------

#ifdef __cplusplus
void* _mi_externs[] = {
  (void*)&_mi_page_malloc,
  (void*)&_mi_heap_malloc_zero,
  (void*)&_mi_heap_malloc_zero_ex,
  (void*)&mi_malloc,
  (void*)&mi_malloc_small,
  (void*)&mi_zalloc_small,
  (void*)&mi_heap_malloc,
  (void*)&mi_heap_zalloc,
  (void*)&mi_heap_malloc_small,
  (void*)&mi_heap_alloc_new,
  (void*)&mi_heap_alloc_new_n
};
#endif
