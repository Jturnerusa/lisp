use std::cell::Cell;
use std::marker::PhantomData;
use std::ptr::NonNull;

thread_local! {
    pub static HEAD: Cell<Option<NonNull<Inner<dyn Trace>>>> = Cell::new(None);
}

pub unsafe trait Trace {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>));
}

pub struct Inner<T: Trace + ?Sized> {
    next: Cell<Option<NonNull<Inner<dyn Trace>>>>,
    prev: Cell<Option<NonNull<Inner<dyn Trace>>>>,
    refs: Cell<usize>,
    data: T,
}

pub struct Gc<T: Trace + ?Sized> {
    inner: NonNull<Inner<T>>,
    phantom: PhantomData<T>,
}

pub fn collect() {
    let mut cursor = HEAD.get();
    while let Some(current) = cursor {
        unsafe {
            cursor = current.as_ref().next.get();
            if current.as_ref().refs.get() == 0 {
                if let Some(prev) = current.as_ref().prev.get() {
                    prev.as_ref().next.set(current.as_ref().next.get());
                    if let Some(next) = current.as_ref().next.get() {
                        next.as_ref().prev.set(Some(prev))
                    }
                } else {
                    HEAD.set(current.as_ref().next.get());
                    if let Some(next) = current.as_ref().next.get() {
                        next.as_ref().prev.set(HEAD.get());
                    }
                }
                std::mem::drop(Box::from_raw(current.as_ptr()));
            }
        }
    }
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
            inner: self.inner,
            phantom: PhantomData,
        }
    }
}

impl<T: Trace + ?Sized> Drop for Gc<T> {
    fn drop(&mut self) {
        unsafe {
            let refs = self.inner.as_ref().refs.get();
            self.inner.as_ref().refs.set(refs.checked_sub(1).unwrap())
        }
    }
}

unsafe impl<T: Trace + 'static> Trace for Gc<T> {
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>)) {
        tracer(self.inner)
    }
}
