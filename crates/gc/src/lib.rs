#![allow(dead_code)]

mod cell;
mod gc;

pub use crate::cell::GcCell;
pub use crate::gc::Gc;
pub use crate::gc::Inner;

use std::cell::Cell;
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::mem;
use std::ptr::NonNull;

thread_local! {
    pub static HEAD: Cell<Option<NonNull<Inner<dyn Trace>>>> = Cell::new(None);
    pub static HEAP_SIZE: Cell<usize> = Cell::new(1024usize.pow(2));
    pub static CURRENT_SIZE: Cell<usize> = Cell::new(0);
}

#[allow(clippy::missing_safety_doc)]
pub unsafe trait Trace {
    unsafe fn root(&self);
    unsafe fn unroot(&self);
    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>) -> bool);
}

pub fn set_heap_size(size: usize) {
    HEAP_SIZE.set(size);
}

pub fn collect() {
    let mut cursor = HEAD.get();
    while let Some(current) = cursor {
        let current_ref = unsafe { current.as_ref() };
        cursor = current_ref.next.get();
        current_ref.marked.set(false);
    }

    let mut cursor = HEAD.get();
    while let Some(current) = cursor {
        let current_ref = unsafe { current.as_ref() };
        cursor = current_ref.next.get();

        if current_ref.refs.get() > 0 {
            current_ref.traced.set(true);
            current_ref.marked.set(true);

            unsafe {
                current_ref.data.trace(&mut |inner| {
                    let inner = inner.as_ref();

                    inner.marked.set(true);

                    if inner.traced.get() {
                        false
                    } else {
                        inner.traced.set(true);
                        true
                    }
                });
            };
        }
    }

    let mut cursor = HEAD.get();
    while let Some(current) = cursor {
        let current_ref = unsafe { current.as_ref() };
        cursor = current_ref.next.get();

        if !current_ref.marked.get() {
            unsafe {
                remove_from_list(current);
                mem::drop(Box::from_raw(current.as_ptr()));
            };
        }
    }
}

pub(crate) unsafe fn add_to_list(inner: NonNull<Inner<dyn Trace>>) {
    let inner_ref = inner.as_ref();

    CURRENT_SIZE.set(CURRENT_SIZE.get() + mem::size_of_val(&inner_ref.data));

    if CURRENT_SIZE.get() > HEAP_SIZE.get() {
        collect();
    }

    if let Some(head) = HEAD.get() {
        let head_ref = head.as_ref();
        inner_ref.next.set(Some(head));
        head_ref.prev.set(Some(inner));
    }

    HEAD.set(Some(inner));
}

pub(crate) unsafe fn remove_from_list(inner: NonNull<Inner<dyn Trace>>) {
    let inner_ref = inner.as_ref();

    CURRENT_SIZE.set(CURRENT_SIZE.get() - mem::size_of_val(&inner_ref.data));

    let next = inner_ref.next.get();
    let prev = inner_ref.prev.get();

    if let Some(next) = next {
        let next_ref = next.as_ref();
        next_ref.prev.set(prev);
    }

    if let Some(prev) = prev {
        let prev_ref = prev.as_ref();
        prev_ref.next.set(next);
    } else {
        HEAD.set(next);
    }
}

unsafe impl Trace for String {
    unsafe fn root(&self) {}
    unsafe fn unroot(&self) {}
    unsafe fn trace(&self, _: &mut dyn FnMut(NonNull<Inner<dyn Trace>>) -> bool) {}
}

unsafe impl<T: Trace> Trace for &[T] {
    unsafe fn root(&self) {
        for element in *self {
            element.root();
        }
    }

    unsafe fn unroot(&self) {
        for element in *self {
            element.unroot();
        }
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>) -> bool) {
        for element in *self {
            element.trace(tracer);
        }
    }
}

unsafe impl<T: Trace> Trace for Vec<T> {
    unsafe fn root(&self) {
        self.as_slice().root();
    }

    unsafe fn unroot(&self) {
        self.as_slice().unroot();
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>) -> bool) {
        self.as_slice().trace(tracer);
    }
}

unsafe impl<K: Trace, V: Trace, S: BuildHasher> Trace for HashMap<K, V, S> {
    unsafe fn root(&self) {
        for (k, v) in self {
            k.root();
            v.root();
        }
    }

    unsafe fn unroot(&self) {
        for (k, v) in self {
            k.unroot();
            v.unroot();
        }
    }

    unsafe fn trace(&self, tracer: &mut dyn FnMut(NonNull<Inner<dyn Trace>>) -> bool) {
        for (k, v) in self {
            k.trace(tracer);
            v.trace(tracer);
        }
    }
}
