use ic_cdk::api::stable::{StableMemory};
use crate::memory::{Address, AllocationError, Memory, PagedMemory, WASM_PAGE_SIZE_IN_BYTES};

impl Memory for dyn StableMemory {
    fn size_in_pages(&self) -> u64 {
        <Self as StableMemory>::stable64_size(self)
    }

    fn grow(&self, new_pages: u64) -> Result<u64, AllocationError> {
        <Self as StableMemory>::stable64_grow(self, new_pages)
            .map_err(|_| AllocationError::new())
    }

    fn write(&self, offset: Address, buf: &[u8]) {
        <Self as StableMemory>::stable64_write(self, offset.0, buf)
    }

    fn read(&self, offset: Address, buf: &mut [u8]) {
        <Self as StableMemory>::stable64_read(self, offset.0, buf)
    }
}

impl PagedMemory for dyn StableMemory {
    const PAGE_SIZE_IN_BYTES: usize = WASM_PAGE_SIZE_IN_BYTES;
}