use std::marker::PhantomData;
use std::mem::{MaybeUninit, size_of};
use std::ops::Deref;
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
    // pub fn offset(&self, offset: isize) -> Self {
    //     Self::from_address((self.inner as isize + offset) as u64)
    // }
    pub fn byte_address(&self) -> u64 {
        self.inner
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
        self.write(Address(offset.byte_address()), unsafe { from_raw_parts(value as *const T as *const _, size_of::<T>()) })
    }
    fn read_value<T>(&self, offset: TypedAddress<T>, value: *mut T) {
        self.read(Address(offset.byte_address()), unsafe { from_raw_parts_mut(value as *mut _, size_of::<T>()) })
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

struct Pointer<MR: Deref>
    where MR::Target: MemoryExt
{
    pub memory: MR,
    pub address: Address,
}

impl<MR: Deref> Pointer<MR>
    where MR::Target: MemoryExt
{
    pub fn new(memory: MR, address: Address) -> Self {
        Self {
            memory,
            address,
        }
    }
    pub fn byte_address(&self) -> u64 {
        self.address.0
    }
}

impl<MR: Deref> Pointer<MR>
    where MR::Target: MemoryExt
{
    fn write(&self, value: &[u8]) {
        self.memory.write(self.address, value)
    }
    fn read(&self, value: &mut [u8]) {
        self.memory.read(self.address, value)
    }
}

struct TypedPointer<T, MR: Deref>
    where MR::Target: MemoryExt
{
    pub memory: MR,
    pub address: TypedAddress<T>,
}

impl<T, MR: Deref> TypedPointer<T, MR>
    where MR::Target: MemoryExt
{
    pub fn new(memory: MR, address: TypedAddress<T>) -> Self {
        Self {
            memory,
            address,
        }
    }
    pub fn byte_address(&self) -> u64 {
        self.address.byte_address()
    }
}

impl<T, MR: Deref> Typed for TypedPointer<T, MR>
    where MR::Target: MemoryExt
{
    type Type = T;
}

impl<T, MR: Deref> TypedPointer<T, MR>
    where MR::Target: MemoryExt
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
    ($pointer:expr=>$field:ident,$value:expr) => {
        {
            use offset::offset_of;
            $mem.write_value($pointer.byte_address() + offset_of!(<$addr::Type>::$field).as_u32() as usize, $value)
        }
    };
}

/// `read_field!(pointer=>field, pointer)`
macro_rules! read_field {
    ($pointer:expr=>$field:ident,$to:expr) => {
        {
            use offset::offset_of;
            $pointer.read_value($pointer.byte_address() + offset_of!(<$addr::Type>::$field).as_u32() as usize, $to)
        }
    };
}

/// `return_field!(pointer=>field)`
macro_rules! return_field {
    ($pointer:expr=>$field:ident) => {
        {
            use offset::offset_of;
            $pointer.return_value($pointer.byte_address() + offset_of!(<$pointer::Type>::$field).as_u32() as usize)
        }
    };
}

/// `update_field!(pointer=>field, update)`
macro_rules! update_field {
    ($pointer:expr=>$field:ident,$update:expr) => {
        {
            use offset::offset_of;
            $pointer.update_value($pointer.byte_address() + offset_of!(<$pointer::Type>::$field).as_u32() as usize, update)
        }
    };
}

pub(crate) use write_field;
pub(crate) use read_field;
pub(crate) use return_field;
pub(crate) use update_field;
