use crate::Trace;
use std::cell::Cell;
use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::NonNull;

#[derive(Debug)]
pub struct Inner<T: Trace + ?Sized> {
    pub(crate) next: Cell<Option<NonNull<Inner<dyn Trace>>>>,
    pub(crate) prev: Cell<Option<NonNull<Inner<dyn Trace>>>>,
    pub(crate) refs: Cell<usize>,
    pub(crate) traced: Cell<bool>,
    pub(crate) marked: Cell<bool>,
    pub(crate) data: T,
}

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
            traced: Cell::new(false),
            marked: Cell::new(false),
            data,
        }
    }
}

impl<T: Trace + ?Sized> Inner<T> {
    fn increment_refs(&self) {
        let refs = self.refs.get();
        let i = refs.checked_add(1).unwrap();
        self.refs.set(i);
    }

    fn decrement_refs(&self) {
        let refs = self.refs.get();
        let i = refs.checked_sub(1).unwrap();
        self.refs.set(i);
    }
}

impl<T: Trace + 'static> Gc<T> {
    pub fn new(data: T) -> Self {
        unsafe {
            data.unroot();
        };

        let inner = NonNull::new(Box::into_raw(Box::new(Inner::new(data)))).unwrap();

        unsafe {
            crate::add_to_list(inner);
        };

        Self {
            rooted: Cell::new(true),
            inner,
            phantom: PhantomData,
        }
    }
}

impl<T: Trace + ?Sized> Clone for Gc<T> {
    fn clone(&self) -> Self {
        unsafe {
            self.inner.as_ref().increment_refs();
        };
        Self {
            rooted: Cell::new(true),
            inner: self.inner,
            phantom: PhantomData,
        }
    }
}

impl<T: Trace + ?Sized> Drop for Gc<T> {
    fn drop(&mut self) {
        if self.rooted.get() {
            unsafe {
                self.inner.as_ref().decrement_refs();
            };
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

impl<T: Trace + fmt::Debug> fmt::Debug for Gc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Gc")
            .field("inner", unsafe { &self.inner.as_ref().data })
            .field("rooted", &self.rooted.get())
            .finish()
    }
}

unsafe impl<T: Trace + 'static> Trace for Gc<T> {
    unsafe fn root(&self) {
        debug_assert!(!self.rooted.get());

        self.rooted.set(true);

        let inner_ref = unsafe { self.inner.as_ref() };

        inner_ref.increment_refs();
    }

    unsafe fn unroot(&self) {
        debug_assert!(self.rooted.get());

        self.rooted.set(false);

        let inner_ref = unsafe { self.inner.as_ref() };

        inner_ref.decrement_refs();
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>) -> bool) {
        if tracer(self.inner) {
            self.inner.as_ref().data.trace(tracer);
        }
    }
}
