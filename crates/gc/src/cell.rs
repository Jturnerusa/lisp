use crate::Trace;
use std::{
    cell::{Cell, UnsafeCell},
    fmt::Display,
    num::NonZeroUsize,
    ops::{Deref, DerefMut},
};

#[derive(Clone, Copy, Debug)]
enum State {
    Shared(NonZeroUsize),
    Exclusive,
    None,
}

#[derive(Debug)]
pub struct Ref<'a, T: Trace> {
    data: &'a T,
    state: &'a Cell<State>,
}

#[derive(Debug)]
pub struct RefMut<'a, T: Trace> {
    data: &'a mut T,
    state: &'a Cell<State>,
    rooted: bool,
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct GcCell<T: Trace> {
    data: UnsafeCell<T>,
    state: Cell<State>,
    rooted: Cell<bool>,
}

impl<T: Trace> GcCell<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: UnsafeCell::new(data),
            state: Cell::new(State::None),
            rooted: Cell::new(true),
        }
    }

    pub fn try_borrow(&self) -> Option<Ref<'_, T>> {
        self.state.set(match self.state.get() {
            State::Shared(n) => State::Shared(NonZeroUsize::new(n.get() + 1).unwrap()),
            State::None => State::Shared(NonZeroUsize::new(1).unwrap()),
            State::Exclusive => return None,
        });
        Some(Ref {
            data: unsafe { self.data.get().as_ref().unwrap() },
            state: &self.state,
        })
    }

    pub fn try_borrow_mut(&self) -> Option<RefMut<'_, T>> {
        self.state.set(match self.state.get() {
            State::Shared(_) | State::Exclusive => return None,
            State::None => State::Exclusive,
        });
        if self.rooted.get() {
            unsafe {
                self.data.get().as_ref().unwrap().root();
            };
        }
        Some(RefMut {
            data: unsafe { self.data.get().as_mut().unwrap() },
            state: &self.state,
            rooted: self.rooted.get(),
        })
    }

    pub fn borrow(&self) -> Ref<'_, T> {
        self.try_borrow().unwrap()
    }

    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        self.try_borrow_mut().unwrap()
    }
}

impl<'a, T: Trace> Drop for Ref<'a, T> {
    fn drop(&mut self) {
        self.state.set(match self.state.get() {
            State::Shared(n) if n.get() > 1 => {
                State::Shared(NonZeroUsize::new(n.get() - 1).unwrap())
            }
            State::Shared(n) if n.get() == 1 => State::None,
            _ => unreachable!(),
        });
    }
}

impl<'a, T: Trace> Drop for RefMut<'a, T> {
    fn drop(&mut self) {
        self.state.set(State::None);
        if self.rooted {
            unsafe {
                self.data.unroot();
            };
        }
    }
}

impl<'a, T: Trace> Deref for Ref<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.data
    }
}

impl<'a, T: Trace> Deref for RefMut<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.data
    }
}

impl<'a, T: Trace> DerefMut for RefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data
    }
}

unsafe impl<T: Trace> Trace for GcCell<T> {
    unsafe fn root(&self) {
        debug_assert!(!self.rooted.get());

        self.rooted.set(true);

        if let State::Shared(_) | State::None = self.state.get() {
            unsafe {
                self.data.get().as_ref().unwrap().root();
            }
        }
    }

    unsafe fn unroot(&self) {
        debug_assert!(self.rooted.get());

        self.rooted.set(false);

        if let State::Shared(_) | State::None = self.state.get() {
            unsafe {
                self.data.get().as_ref().unwrap().unroot();
            }
        }
    }

    unsafe fn trace(
        &self,
        tracer: &mut dyn FnMut(std::ptr::NonNull<crate::gc::Inner<dyn Trace>>) -> bool,
    ) {
        self.borrow().trace(tracer);
    }
}

impl<T: Trace + PartialEq> PartialEq for GcCell<T> {
    fn eq(&self, other: &Self) -> bool {
        *self.borrow() == *other.borrow()
    }
}

impl<T: Trace + Eq> Eq for GcCell<T> {}

impl<T: Trace + PartialOrd> PartialOrd for GcCell<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.borrow().partial_cmp(&*other.borrow())
    }
}

impl<T: Trace + Ord> Ord for GcCell<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.borrow().cmp(&*other.borrow())
    }
}

impl<T: Trace + Display> Display for GcCell<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.borrow().fmt(f)
    }
}

impl<T: Trace + Clone> Clone for GcCell<T> {
    fn clone(&self) -> Self {
        GcCell::new(self.borrow().clone())
    }
}
