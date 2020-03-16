#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::boxed::Box;
use core::{
    ptr::NonNull,
    sync::atomic::{AtomicPtr, Ordering},
};

pub struct TreiberStack<T> {
    top: AtomicPtr<Node<T>>,
}

impl<T> TreiberStack<T> {
    #[inline]
    pub fn new() -> Self {
        Self {
            top: AtomicPtr::new(0 as *mut Node<T>),
        }
    }

    #[inline]
    pub fn push(&self, item: T) {
        let mut new_head = Box::into_raw(Box::new(Node::new(item)));
        let mut old_head;

        while {
            old_head = self.top.load(Ordering::SeqCst);
            unsafe {
                // If the current `top` pointer is null, `next` will be None
                (*new_head).next = NonNull::<Node<T>>::new(old_head);
            }

            self.top
                .compare_and_swap(old_head, new_head, Ordering::SeqCst)
                != old_head
        } {}
    }

    #[inline]
    pub fn pop(&self) -> Option<T> {
        let mut old_head;
        let mut new_head;

        while {
            old_head = self.top.load(Ordering::SeqCst);

            if old_head.is_null() {
                return None;
            }

            new_head = unsafe {
                (*old_head)
                    .next
                    .map(|p| p.as_ptr())
                    .unwrap_or(0 as *mut Node<T>)
            };

            self.top
                .compare_and_swap(old_head, new_head, Ordering::SeqCst)
                != old_head
        } {}

        let old_head = unsafe { Box::from_raw(old_head) };

        Some(old_head.item)
    }

    #[inline]
    pub fn take(&self) -> Option<Box<Node<T>>> {
        let mut old_head;
        let new_head = 0 as *mut Node<T>;

        while {
            old_head = self.top.load(Ordering::SeqCst);

            if old_head.is_null() {
                return None;
            }

            self.top
                .compare_and_swap(old_head, new_head, Ordering::SeqCst)
                != old_head
        } {}

        let old_head = unsafe { Box::from_raw(old_head) };

        Some(old_head)
    }
}

unsafe impl<T> Send for TreiberStack<T> {}
unsafe impl<T> Sync for TreiberStack<T> {}

pub struct Node<T> {
    item: T,
    next: Option<NonNull<Node<T>>>,
}

impl<T> Node<T> {
    #[inline]
    pub fn new(item: T) -> Self {
        Self { item, next: None }
    }
}

#[cfg(test)]
mod tests {
    use super::TreiberStack;
    use std::{sync::Arc, thread};

    #[test]
    fn smoke() {
        let stack = TreiberStack::new();
        stack.push(100usize);
        assert_eq!(Some(100usize), stack.pop());
        stack.push(200usize);
        assert_eq!(Some(200usize), stack.pop());
        stack.push(300usize);
        assert_eq!(Some(300usize), stack.pop());
        stack.push(400usize);
        assert_eq!(Some(400usize), stack.pop());

        for i in 0..100 {
            stack.push(i);
        }

        for i in (0..100).rev() {
            assert_eq!(Some(i), stack.pop());
        }
        assert!(stack.pop().is_none());
    }

    #[test]
    fn high_contention() {
        let stack = Arc::new(TreiberStack::new());

        let mut threads = Vec::with_capacity(100);
        for _ in 0..100 {
            let s = Arc::clone(&stack);
            threads.push(thread::spawn(move || {
                for i in 0..10 {
                    s.push(i);
                }
            }));
        }

        let _ = threads
            .into_iter()
            .map(|t| t.join().unwrap())
            .collect::<Vec<()>>();

        while let Some(val) = stack.pop() {
            let _ = val;
        }
    }
}
