use core::fmt;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};
use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::NonNull;

thread_local! {
    pub static HEAD: Cell<Option<NonNull<Inner<dyn Trace>>>> = Cell::new(None);
}

pub unsafe trait Trace {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>));
}

#[repr(C)]
#[derive(Debug)]
pub struct Inner<T: Trace + ?Sized> {
    next: Cell<Option<NonNull<Inner<dyn Trace>>>>,
    prev: Cell<Option<NonNull<Inner<dyn Trace>>>>,
    refs: Cell<usize>,
    data: T,
}

#[derive(Debug)]
pub struct Gc<T: Trace + ?Sized> {
    rooted: Cell<bool>,
    inner: NonNull<Inner<T>>,
    phantom: PhantomData<T>,
}

impl<T: Trace> Inner<T> {
    fn new(data: T) -> Self {
        Self {
            next: Cell::new(None),
            prev: Cell::new(None),
            refs: Cell::new(1),
            data,
        }
    }
}

impl<T: Trace + 'static> Gc<T> {
    pub fn new(data: T) -> Self {
        let inner = Box::into_raw(Box::new(Inner::new(data)));
        let nonnull = NonNull::new(inner).unwrap();

        let head = HEAD.get();

        if let Some(head) = head {
            unsafe {
                nonnull.as_ref().next.set(Some(head));
                head.as_ref().prev.set(Some(nonnull));
            }
        }

        HEAD.set(Some(nonnull));

        Self {
            rooted: Cell::new(true),
            inner: nonnull,
            phantom: PhantomData,
        }
    }
}

impl<T: Trace + ?Sized> Clone for Gc<T> {
    fn clone(&self) -> Self {
        unsafe {
            let refs = self.inner.as_ref().refs.get();
            self.inner.as_ref().refs.set(refs.checked_add(1).unwrap());
        }
        Self {
            rooted: Cell::new(true),
            inner: self.inner,
            phantom: PhantomData,
        }
    }
}

impl<T: Trace + ?Sized> Deref for Gc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &self.inner.as_ref().data }
    }
}

impl<T: Trace + PartialEq + ?Sized> PartialEq for Gc<T> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let a = &self.inner.as_ref().data;
            let b = &other.inner.as_ref().data;
            a == b
        }
    }
}

impl<T: Trace + Eq + ?Sized> Eq for Gc<T> {}

impl<T: Trace + PartialOrd + ?Sized> PartialOrd for Gc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        unsafe {
            let a = &self.inner.as_ref().data;
            let b = &other.inner.as_ref().data;
            a.partial_cmp(b)
        }
    }
}

impl<T: Trace + Ord + ?Sized> Ord for Gc<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        unsafe {
            let a = &self.inner.as_ref().data;
            let b = &other.inner.as_ref().data;
            a.cmp(b)
        }
    }
}

impl<T: Trace + Hash + ?Sized> Hash for Gc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe {
            self.inner.as_ref().data.hash(state);
        }
    }
}

impl<T: Trace + fmt::Display> fmt::Display for Gc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe { self.inner.as_ref().data.fmt(f) }
    }
}

unsafe impl<T: Trace + 'static> Trace for Gc<T> {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>)) {
        tracer(self.inner);
    }
}

unsafe impl<T: Trace> Trace for RefCell<T> {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>)) {
        self.borrow().deref().trace(tracer);
    }
}

unsafe impl Trace for String {
    unsafe fn trace(&self, _: &mut dyn FnMut(NonNull<Inner<dyn Trace>>)) {}
}

unsafe impl<T: Trace> Trace for [T] {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>)) {
        for element in self {
            element.trace(tracer);
        }
    }
}

unsafe impl<T: Trace> Trace for Vec<T> {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>)) {
        for element in self {
            element.trace(tracer);
        }
    }
}

unsafe impl<K: Trace, V: Trace, H: BuildHasher> Trace for HashMap<K, V, H> {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>)) {
        for (key, val) in self {
            key.trace(tracer);
            val.trace(tracer);
        }
    }
}
