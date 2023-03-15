use std::ops::Deref;
use std::sync::atomic::AtomicU64;
use ic_cdk::api::stable::{CanisterStableMemory, StableMemory};
use crate::memory::{AllocationError, Memory, PagedMemory};

pub const WASM_PAGE_SIZE_IN_BYTES: usize = 64 * 1024; // 64KB

impl Memory for dyn StableMemory {
    type Address = u64;
    type Size = u64;
    type PtrDiff = i64;
    type AtomicAddress = AtomicU64;
    type AtomicSize = AtomicU64;

    fn size_in_pages(&self) -> Self::Size {
        <Self as StableMemory>::stable64_size(self)
    }

    fn grow(&self, new_pages: Self::Size) -> Result<Self::Size, AllocationError> {
        <Self as StableMemory>::stable64_grow(self, new_pages)
            .map_err(|_| AllocationError::new())
    }

    fn write(&self, offset: Self::Address, buf: &[u8]) {
        <Self as StableMemory>::stable64_write(self, offset, buf)
    }

    fn read(&self, offset: Self::Address, buf: &mut [u8]) {
        <Self as StableMemory>::stable64_read(self, offset, buf)
    }
}

impl PagedMemory for dyn StableMemory {
    const PAGE_SIZE_IN_BYTES: usize = WASM_PAGE_SIZE_IN_BYTES;
}

/// Its advantage over `&CanisterStableMemory` is that `CanisterStableMemoryRef` is zero-size.
struct CanisterStableMemoryRef;

impl Deref for CanisterStableMemoryRef {
    type Target = CanisterStableMemory;

    fn deref(&self) -> &Self::Target {
        &CanisterStableMemory {}
    }
}

