use std::mem::{MaybeUninit, size_of};
use std::slice::{from_raw_parts, from_raw_parts_mut};
use ic_cdk::api::stable::{StableMemory, StableMemoryError};

pub struct Address(pub u64);

pub const WASM_PAGE_SIZE_IN_BYTES: usize = 64 * 1024; // 64KB

pub trait Memory {
    const PAGE_SIZE_IN_BYTES: usize;
    fn size_in_pages(&self) -> u64;
    fn grow(&self, new_pages: u64) -> Result<u64, StableMemoryError>;
    fn write(&self, offset: Address, buf: &[u8]);
    fn read(&self, offset: Address, buf: &mut [u8]);

    fn write_value<T>(&self, offset: Address, value: &T) {
        self.write(offset, unsafe { from_raw_parts(value as *const T as *const _, size_of::<T>()) })
    }
    fn read_value<T>(&self, offset: Address, value: *mut T) { // Creating a reference with &/&mut is only allowed if the pointer is properly aligned and points to initialized data.
        self.read(offset, unsafe { from_raw_parts_mut(value as *mut _, size_of::<T>()) })
    }
    fn return_value<T>(&self, offset: Address) -> T {
        let mut x = MaybeUninit::<T>::uninit();
        self.read_value(offset, &mut x);
        unsafe { x.assume_init() }
    }
}

impl Memory for dyn StableMemory {
    const PAGE_SIZE_IN_BYTES: usize = WASM_PAGE_SIZE_IN_BYTES;

    fn size_in_pages(&self) -> u64 {
        <Self as StableMemory>::stable64_size(self)
    }

    fn grow(&self, new_pages: u64) -> Result<u64, StableMemoryError> {
        <Self as StableMemory>::stable64_grow(self, new_pages)
    }

    fn write(&self, offset: Address, buf: &[u8]) {
        <Self as StableMemory>::stable64_write(self, offset.0, buf)
    }

    fn read(&self, offset: Address, buf: &mut [u8]) {
        <Self as StableMemory>::stable64_read(self, offset.0, buf)
    }
}

/// `write_field!(memory, address, C::f, value)`
macro_rules! write_field {
    ($mem:expr,$addr:expr,$ty:ident::$field:ident,$value:expr) => {
        $mem.write_value(($addr) + offset_of!($ty::$field).as_u32() as usize, $value)
    };
    ($mem:expr,$addr:expr,<$ty:path>::$field:ident,$value:expr) => {
        $mem.write_value(($addr) + offset_of!(<$ty:path>::$field).as_u32() as usize, $value)
    };
}

/// `read_field!(memory, address, C::f, pointer)`
macro_rules! read_field {
    ($mem:expr,$addr:expr,$ty:ident::$field:ident,$pointer:expr) => {
        $mem.read_value(($addr) + offset_of!($ty::$field).as_u32() as usize, $pointer)
    };
    ($mem:expr,$addr:expr,<$ty:path>::$field:ident,$pointer:expr) => {
        $mem.read_value(($addr) + offset_of!(<$ty:path>::$field).as_u32() as usize, $pointer)
    };
}

/// `return_field!(memory, address, C::f)`
macro_rules! return_field {
    ($mem:expr,$addr:expr,$ty:ident::$field:ident) => {
        $mem.return_value($addr + offset_of!($ty::$field).as_u32() as usize)
    };
    ($mem:expr,$addr:expr,<$ty:path>::$field:ident) => {
        $mem.return_value($addr + offset_of!(<$ty:path>::$field).as_u32() as usize)
    };
}

pub(crate) use write_field;
pub(crate) use read_field;
pub(crate) use return_field;
