use std::marker::PhantomData;
use std::mem::{MaybeUninit, size_of};
use std::ops::Deref;
use std::slice::{from_raw_parts, from_raw_parts_mut};
use derive_more::Display;
use num_traits::{int::PrimInt, sign::Unsigned};

#[derive(new)]
#[derive(Display)]
#[display(fmt = "Memory allocation error.")]
pub struct AllocationError;

pub trait Memory {
    type Address: PrimInt + Unsigned;
    type Size: PrimInt + Unsigned;
    fn size_in_pages(&self) -> u64;
    fn grow(&self, new_pages: u64) -> Result<u64, AllocationError>;
    fn write(&self, offset: Self::Address, buf: &[u8]);
    fn read(&self, offset: Self::Address, buf: &mut [u8]);
}

// #[derive(Clone, Copy)]
// pub struct Address(pub u64);

trait Typed {
    type Type;
}

pub struct TypedAddress<M: Memory + ?Sized, T>{
    inner: M::Address,
    phantom: PhantomData<T>,
}

impl<M: Memory + ?Sized, T> TypedAddress<M, T> {
    pub fn from_address(addr: M::Address) -> Self {
        Self {
            inner: addr,
            phantom: PhantomData,
        }
    }
    // pub fn offset(&self, offset: isize) -> Self {
    //     Self::from_address((self.inner as isize + offset) as u64)
    // }
    pub fn byte_address(&self) -> M::Address {
        self.inner
    }
}

impl<M: Memory + ?Sized, T> Clone for TypedAddress<M, T>
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<M: Memory + ?Sized, T> Copy for TypedAddress<M, T>
{}

impl<M: Memory + ?Sized, T> Typed for TypedAddress<M, T> {
    type Type = T;
}

pub trait PagedMemory {
    const PAGE_SIZE_IN_BYTES: usize;
}

pub trait MemoryRef: Deref
    where Self::Target: Memory
{
    fn write_value<T>(&self, offset: TypedAddress<Self::Target, T>, value: &T) {
        self.write(offset.byte_address(), unsafe { from_raw_parts(value as *const T as *const _, size_of::<T>()) })
    }
    fn read_value<T>(&self, offset: TypedAddress<Self::Target, T>, value: *mut T) {
        self.read(offset.byte_address(), unsafe { from_raw_parts_mut(value as *mut _, size_of::<T>()) })
    }
    fn return_value<T>(&self, offset: TypedAddress<Self::Target, T>) -> T {
        let mut x = MaybeUninit::<T>::uninit();
        self.read_value(offset, x.as_mut_ptr());
        unsafe { x.assume_init() }
    }
    fn update_value<T, F>(&self, offset: TypedAddress<Self::Target, T>, update: F)
        where F: FnOnce(T) -> T
    {
        let old = self.return_value(offset);
        let new = update(old);
        self.write_value(offset, &new);
    }
}

struct Pointer<MR: MemoryRef>
    where MR::Target: Memory
{
    pub memory: MR,
    pub address: <MR::Target as Memory>::Address,
}

impl<MR: MemoryRef> Pointer<MR>
    where MR::Target: Memory
{
    pub fn new(memory: MR, address: <MR::Target as Memory>::Address) -> Self {
        Self {
            memory,
            address,
        }
    }
    pub fn byte_address(&self) -> <MR::Target as Memory>::Address {
        self.address
    }
}

impl<MR: MemoryRef> Pointer<MR>
    where MR::Target: Memory
{
    fn write(&self, value: &[u8]) {
        self.memory.write(self.address, value)
    }
    fn read(&self, value: &mut [u8]) {
        self.memory.read(self.address, value)
    }
}

struct TypedPointer<MR: MemoryRef, T>
    where MR::Target: Memory
{
    pub memory: MR,
    pub address: TypedAddress<MR::Target, T>,
}

impl<T, MR: MemoryRef> TypedPointer<MR, T>
    where MR::Target: Memory
{
    pub fn new(memory: MR, address: TypedAddress<MR::Target, T>) -> Self {
        Self {
            memory,
            address,
        }
    }
    pub fn byte_address(&self) -> <MR::Target as Memory>::Address {
        self.address.byte_address()
    }
}

impl<T, MR: MemoryRef> Typed for TypedPointer<MR, T>
    where MR::Target: Memory
{
    type Type = T;
}

impl<T, MR: MemoryRef> TypedPointer<MR, T>
    where MR::Target: Memory
{
    fn write_value(&self, value: &T) {
        self.memory.write_value(self.address, value)
    }
    fn read_value(&self, value: *mut T) {
        self.memory.read_value(self.address, value)
    }
    pub fn return_value(&self) -> T {
        self.memory.return_value(self.address)
    }
}

/// `write_field!(pointer=>field, value)`
macro_rules! write_field {
    ($pointer:expr,$s:ident=>$field:ident,$value:expr) => {
        {
            use offset::offset_of;
            $pointer.memory.write_value($pointer.byte_address() + offset_of!($s::$field).as_u32() as usize, $value)
        }
    };
}

/// `read_field!(pointer=>field, pointer)`
macro_rules! read_field {
    ($pointer:expr,$s:ident=>$field:ident,$to:expr) => {
        {
            use offset::offset_of;
            $pointer.memory.read_value($pointer.byte_address() + offset_of!($s::$field).as_u32() as usize, $to)
        }
    };
}

/// `return_field!(pointer=>field)`
macro_rules! return_field {
    ($pointer:expr,$s:ident=>$field:ident) => {
        {
            use offset::offset_of;
            $pointer.memory.return_value($pointer.byte_address() + offset_of!($s::$field).as_u32() as usize)
        }
    };
}

/// `update_field!(pointer=>field, update)`
macro_rules! update_field {
    ($pointer:expr,$s:ident=>$field:ident,$update:expr) => {
        {
            use offset::offset_of;
            $pointer.memory.update_value($pointer.byte_address() + offset_of!($s::$field).as_u32() as usize, update)
        }
    };
}

pub(crate) use write_field;
pub(crate) use read_field;
pub(crate) use return_field;
pub(crate) use update_field;
