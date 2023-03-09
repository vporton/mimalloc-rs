use std::marker::PhantomData;
use std::mem::{MaybeUninit, size_of};
use std::slice::{from_raw_parts, from_raw_parts_mut};
use derive_more::Display;

#[derive(new)]
#[derive(Display)]
#[display(fmt = "Memory allocation error.")]
pub struct AllocationError;

#[derive(Clone, Copy)]
pub struct Address(pub u64);

trait Typed {
    type Type;
}

pub struct TypedAddress<T>{
    inner: u64,
    phantom: PhantomData<T>,
}

impl<T> TypedAddress<T> {
    pub fn from_address(addr: u64) -> Self {
        Self {
            inner: addr,
            phantom: PhantomData,
        }
    }
    pub fn offset(&self, offset: isize) -> Self {
        Self::from_address((self.inner as isize + offset) as u64)
    }
    pub fn byte_address(&self) -> Address {
        Address(self.inner)
    }
}

impl<T> Clone for TypedAddress<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for TypedAddress<T> {}

impl<T> Typed for TypedAddress<T> {
    type Type = T;
}

pub trait PagedMemory {
    const PAGE_SIZE_IN_BYTES: usize;
}

pub trait Memory {
    fn size_in_pages(&self) -> u64;
    fn grow(&self, new_pages: u64) -> Result<u64, AllocationError>;
    fn write(&self, offset: Address, buf: &[u8]);
    fn read(&self, offset: Address, buf: &mut [u8]);
}

pub trait MemoryExt: Memory {
    fn write_value<T>(&self, offset: TypedAddress<T>, value: &T);
    fn read_value<T>(&self, offset: TypedAddress<T>, value: *mut T); // Creating a reference with &/&mut is only allowed if the pointer is properly aligned and points to initialized data.
    fn return_value<T>(&self, offset: TypedAddress<T>) -> T;
    fn update_value<T, F>(&self, offset: TypedAddress<T>, update: F)
        where F: FnOnce(T) -> T;
}

impl MemoryExt for dyn Memory {
    fn write_value<T>(&self, offset: TypedAddress<T>, value: &T) {
        self.write(offset.byte_address(), unsafe { from_raw_parts(value as *const T as *const _, size_of::<T>()) })
    }
    fn read_value<T>(&self, offset: TypedAddress<T>, value: *mut T) {
        self.read(offset.byte_address(), unsafe { from_raw_parts_mut(value as *mut _, size_of::<T>()) })
    }
    fn return_value<T>(&self, offset: TypedAddress<T>) -> T {
        let mut x = MaybeUninit::<T>::uninit();
        self.read_value(offset, x.as_mut_ptr());
        unsafe { x.assume_init() }
    }
    fn update_value<T, F>(&self, offset: TypedAddress<T>, update: F)
        where F: FnOnce(T) -> T
    {
        let old = self.return_value(offset);
        let new = update(old);
        self.write_value(offset, &new);
    }
}


/// `write_field!(memory, address=>field, value)`
macro_rules! write_field {
    ($mem:expr,$addr:expr=>$field:ident,$value:expr) => {
        $mem.write_value($addr + offset_of!(<$addr::Type>::$field).as_u32() as usize, $value)
    };
}

/// `read_field!(memory, address=>field, pointer)`
macro_rules! read_field {
    ($mem:expr,$addr:expr=>$field:ident,$pointer:expr) => {
        $mem.read_value($addr + offset_of!(<$addr::Type>::$field).as_u32() as usize, $pointer)
    };
}

/// `return_field!(memory, address=>field)`
macro_rules! return_field {
    ($mem:expr,$addr:expr=>$field:ident) => {
        $mem.return_value($addr + offset_of!(<$addr::Type>::$field).as_u32() as usize)
    };
}

/// `update_field!(memory, address=>field, update)`
macro_rules! update_field {
    ($mem:expr,$addr:expr=>$field:ident,$update:expr) => {
        $mem.update_value($addr + offset_of!(<$addr::Type>::$field).as_u32() as usize, update)
    };
}

pub(crate) use write_field;
pub(crate) use read_field;
pub(crate) use return_field;
pub(crate) use update_field;
