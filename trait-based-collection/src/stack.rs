//! A collection of different implementations of a stack based on the `LIFO` principle.
//!
//! Currently, the following implementations are available:
//!
//! - [`Stack`]: A linked stack based on nodes.
//! - [`ArrayStack`]: A stack based on an array.
//!
//! For more information, see the respective structs' documentation.
//!
//! For a pure `FIFO` or a mixed `LIFO/FIFO` data structure, see the [`queue`] module.
//!
//! [`queue`]: mod@crate::queue
#![warn(missing_docs)]
use crate::collection::{Collection, ExpansionMode, FixedSizeCollection, Iterators};
use std::iter::Rev;
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::slice::{Iter, IterMut};
use trait_based_collection_macros::{internal_check_expansion_add, iterator, All};

/// A simple-linked node for the basic [`Stack`]. The node contains a value and a pointer to the
/// previous node.
///
/// This struct is not intended to be used directly by the end-user.
#[derive(Debug)]
struct StackNode<T> {
    /// The value stored in the node.
    value: T,
    /// The pointer to the previous node.
    prev: Option<NonNull<StackNode<T>>>,
}

impl<T> StackNode<T> {
    /// Creates a new node with the given value and assigns the previous node to `None`.
    const fn new(value: T) -> Self {
        Self { value, prev: None }
    }
}

/// A stack is a collection that follows the LIFO (last-in-first-out) principle. This means that
/// elements are added to the top of the stack and removed from the top of the stack. This
/// implementation uses a linked-based structure.
///
/// # Examples
/// ```
/// use trait_based_collection::{prelude::*, Stack};
///
/// let mut queue: Stack<u32> = Stack::new_default();
/// queue.add(1);
/// queue.add(2);
/// queue.add(3);
///
/// assert_eq!(queue.peek(), Some(&3));
/// assert_eq!(queue.remove(), Some(3));
/// assert_eq!(queue.remove(), Some(2));
/// assert_eq!(queue.remove(), Some(1));
/// assert_eq!(queue.remove(), None);
/// ```
#[derive(Debug, All)]
pub struct Stack<T> {
    /// The top of the stack.
    top: Option<NonNull<StackNode<T>>>,
    /// The number of elements in the stack.
    len: usize,
}

/// An immutable iterator over the elements of a [`Stack`]. This struct is created by the [`iter`]
/// method on [`Stack`]. See its documentation for more.
///
/// [`iter`]: Stack::iter
pub struct StackIter<'a, T> {
    /// The current node.
    current: Option<NonNull<StackNode<T>>>,
    /// The amount of elements left to iterate over.
    len: usize,
    /// A marker to pin the lifetime of the iterator.
    _marker: PhantomData<&'a T>,
}

impl<'a, T> StackIter<'a, T> {
    /// Creates a new iterator over the elements of the given a reference to a [`Stack`].
    const fn new(stack: &'a Stack<T>) -> Self {
        StackIter {
            current: stack.top,
            len: stack.len,
            _marker: PhantomData,
        }
    }
}

iterator!(Stack, StackIter, ref, {
    let current = self.current.take()?;
    unsafe {
        let current = current.as_ref();
        self.current = current.prev;
        self.len -= 1;
        Some(&current.value)
    }
});

/// A mutable iterator over the elements of a [`Stack`]. This struct is created by the [`iter_mut`]
/// method on [`Stack`]. See its documentation for more.
///
/// [`iter_mut`]: Stack::iter_mut
pub struct StackIterMut<'a, T> {
    /// The current node.
    current: Option<NonNull<StackNode<T>>>,
    /// The amount of elements left to iterate over.
    len: usize,
    /// A marker to pin the lifetime of the iterator.
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> StackIterMut<'a, T> {
    /// Creates a new iterator over the elements of the given a mutable reference to a [`Stack`].
    fn new(stack: &'a mut Stack<T>) -> Self {
        StackIterMut {
            current: stack.top,
            len: stack.len,
            _marker: PhantomData,
        }
    }
}

iterator!(Stack, StackIterMut, mut, {
    let mut current = self.current.take()?;
    unsafe {
        let current = current.as_mut();
        self.current = current.prev;
        self.len -= 1;
        Some(&mut current.value)
    }
});

impl<'a, T: 'a> Iterators<'a, T> for Stack<T> {
    type ItemRef = &'a T;
    type ItemMut = &'a mut T;

    type Iter = StackIter<'a, T>;
    type IterMut = StackIterMut<'a, T>;

    fn iter(&'a self) -> Self::Iter {
        StackIter::new(self)
    }

    fn iter_mut(&'a mut self) -> Self::IterMut {
        StackIterMut::new(self)
    }
}

impl<T> Stack<T> {
    /// Returns a reference to the node at the given index if it exists. The index is 0-based. If
    /// the index is out of bounds, `None` is returned.
    ///
    /// This method is used internally by the [`get`] and [`get_mut`] methods.
    ///
    /// [`get`]: Stack::get
    /// [`get_mut`]: Stack::get_mut
    fn get_node(&self, index: usize) -> Option<NonNull<StackNode<T>>> {
        if index >= self.len || self.is_empty() {
            return None;
        }
        #[allow(clippy::unwrap_used)] // We already the index is valid
        (0..index).fold(self.top, |node, _| unsafe { node.unwrap().as_ref() }.prev)
    }
}

impl<'a, T: 'a> Collection<'a, T> for Stack<T> {
    fn new_default() -> Self {
        Self { top: None, len: 0 }
    }

    fn add(&mut self, value: T) {
        let node = Box::new(StackNode::new(value));
        let mut node_ptr = NonNull::new(Box::into_raw(node)).expect("Failed to allocate memory");

        if let Some(prev) = self.top {
            unsafe { node_ptr.as_mut().prev = Some(prev) };
        }

        self.len += 1;
        self.top = Some(node_ptr);
    }

    fn remove(&mut self) -> Option<T> {
        let node = self.top.take()?;
        self.len -= 1;

        unsafe {
            self.top = node.as_ref().prev;
            Some(Box::from_raw(node.as_ptr()).value)
        }
    }

    fn peek(&'a self) -> Option<Self::ItemRef> {
        self.top.map(|node| unsafe { &node.as_ref().value })
    }

    fn peek_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.top.map(|mut node| unsafe { &mut node.as_mut().value })
    }

    fn get(&'a self, index: usize) -> Option<Self::ItemRef> {
        self.get_node(index)
            .map(|node| unsafe { &node.as_ref().value })
    }

    fn get_mut(&'a mut self, index: usize) -> Option<Self::ItemMut> {
        self.get_node(index)
            .map(|mut node| unsafe { &mut node.as_mut().value })
    }

    fn len(&self) -> usize {
        self.len
    }
}

/// A fixed-size stack capable of expanding when needed. It is implemented using [`Vec`],
/// so the elements are stored contiguously in memory. The main difference between this and a
/// [`Stack`] is that this one does not use nodes.
///
/// Depending on the expansion mode, once the capacity is reached, the deque will behave differently
/// depending on the mode. For more information, see the [`ExpansionMode`] documentation.
///
/// # Examples
/// ```
/// use trait_based_collection::{prelude::*, ArrayStack};
///
/// let mut stack = ArrayStack::with_mode(2, ExpansionMode::Ignore);
/// stack.add(1);
/// stack.add(2);
/// stack.add(3);
///
/// assert_eq!(stack.len(), 2);
/// assert_eq!(stack.remove(), Some(2));
/// assert_eq!(stack.remove(), Some(1));
/// assert_eq!(stack.remove(), None);
/// ```
///
/// [`ExpansionMode`]: crate::collection::ExpansionMode
#[derive(Debug, All)]
pub struct ArrayStack<T> {
    /// A vector containing the elements of the stack.
    data: Vec<T>,
    /// The current mode of expansion of the deque that determinate the behaviour the collection is
    /// full. See [`ExpansionMode`] for more information.
    ///
    /// [`ExpansionMode`]: crate::collection::ExpansionMode
    pub mode: ExpansionMode,
}

impl<'a, T: 'a> Iterators<'a, T> for ArrayStack<T> {
    type ItemRef = &'a T;
    type ItemMut = &'a mut T;

    type Iter = Rev<Iter<'a, T>>;
    type IterMut = Rev<IterMut<'a, T>>;

    fn iter(&'a self) -> Self::Iter {
        self.data.iter().rev()
    }

    fn iter_mut(&'a mut self) -> Self::IterMut {
        self.data.iter_mut().rev()
    }
}

impl<'a, T: 'a> Collection<'a, T> for ArrayStack<T> {
    fn new_default() -> Self {
        Self::with_mode(16, ExpansionMode::default())
    }

    fn with_capacity(capacity: usize) -> Self {
        Self::with_mode(capacity, ExpansionMode::Panic)
    }

    fn with_approximate_capacity(approx_capacity: usize) -> Self {
        Self::with_mode(approx_capacity, ExpansionMode::default())
    }

    #[internal_check_expansion_add]
    fn add(&mut self, value: T) {
        self.data.push(value);
    }

    fn remove(&mut self) -> Option<T> {
        self.data.pop()
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    fn peek(&'a self) -> Option<Self::ItemRef> {
        self.data.last()
    }

    fn peek_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.data.last_mut()
    }

    fn len(&self) -> usize {
        self.data.len()
    }
}

impl<'a, T: 'a> FixedSizeCollection<'a, T> for ArrayStack<T> {
    fn with_mode(capacity: usize, mode: ExpansionMode) -> Self {
        assert_ne!(capacity, 0, "Capacity must be greater than 0");
        Self {
            data: Vec::with_capacity(capacity),
            mode,
        }
    }

    fn capacity(&self) -> usize {
        self.data.capacity()
    }

    fn expand(&mut self, extra_size: usize) {
        self.data
            .reserve(extra_size + self.data.capacity() - self.len());
    }

    fn mode(&self) -> &ExpansionMode {
        &self.mode
    }
}

impl<'a, T> IntoIterator for &'a ArrayStack<T> {
    type Item = &'a T;
    type IntoIter = Rev<Iter<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.data.iter().rev()
    }
}

impl<'a, T> IntoIterator for &'a mut ArrayStack<T> {
    type Item = &'a mut T;
    type IntoIter = Rev<IterMut<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.data.iter_mut().rev()
    }
}

#[cfg(test)]
mod tests_stack {
    use super::*;
    use trait_based_collection_macros::test_collection;

    #[test_collection(Stack, ArrayStack)]
    fn test_add<C: Collection<usize>>(mut stack: C) {
        for i in 0..5 {
            stack.add(i);
        }
        stack.add(usize::MIN);
        stack.add(usize::MAX);
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_remove<C: Collection<usize>>(mut stack: C) {
        assert_eq!(stack.remove(), None);
        for i in 0..5 {
            stack.add(i);
        }
        for i in (0..5_usize).rev() {
            assert_eq!(stack.remove(), Some(i));
        }
        assert_eq!(stack.peek(), None);
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_clear<C: Collection<usize>>(mut stack: C) {
        for i in 0..5 {
            stack.add(i);
        }
        stack.clear();

        assert_eq!(stack.len(), 0);
        assert!(stack.is_empty());
        assert_eq!(stack.peek(), None);
        assert_eq!(stack.remove(), None);
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_peek<C: Collection<usize>>(mut stack: C) {
        assert_eq!(stack.peek(), None);
        for i in 0..5 {
            stack.add(i);
            assert_eq!(stack.peek(), Some(&i));
        }
        for i in (0..5_usize).rev() {
            assert_eq!(stack.peek(), Some(&i));
            stack.remove();
        }
        assert_eq!(stack.peek(), None);
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_peek_mut<C: Collection<usize>>(mut stack: C) {
        assert_eq!(stack.peek_mut(), None);
        for i in 0..5 {
            stack.add(i);
            let peek = stack.peek_mut().unwrap();
            assert_eq!(*peek, i);
            *peek += 1;
        }
        for mut i in (1..6_usize).rev() {
            assert_eq!(stack.peek_mut(), Some(&mut i));
            stack.remove();
        }
        assert_eq!(stack.peek_mut(), None);
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_get<C: Collection<usize>>(mut stack: C) {
        for i in 0..5 {
            stack.add(i);
        }
        for i in 0..5 {
            assert_eq!(*stack.get(i).unwrap(), 4 - i);
        }
        assert_eq!(stack.get(6), None);
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_get_mut<C: Collection<usize>>(mut stack: C) {
        for i in 0..5 {
            stack.add(i);
        }
        for i in 0..5 {
            let get = stack.get_mut(i).unwrap();
            *get += 1;
            assert_eq!(*get, 5 - i);
        }
        assert_eq!(stack.get_mut(6), None);

        for i in (1..6_usize).rev() {
            assert_eq!(stack.remove(), Some(i));
        }
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_find<C: Collection<usize>>(mut stack: C) {
        for i in 0..5 {
            stack.add(i);
        }
        for i in 0..5_usize {
            assert_eq!(stack.find(&i), Some(4 - i));
        }
        assert_eq!(stack.find(&6), None);
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_contains<C: Collection<usize>>(mut stack: C) {
        for i in 0..5 {
            stack.add(i);
        }
        for i in 0..5_usize {
            assert!(stack.contains(&i));
        }
        assert!(!stack.contains(&6));
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_len<C: Collection<usize>>(mut stack: C) {
        assert_eq!(stack.len(), 0);
        for i in 0..5 {
            stack.add(i);
            assert_eq!(stack.len(), i + 1);
        }
        assert_eq!(stack.len(), 5);
        for i in (0..5_usize).rev() {
            stack.remove();
            assert_eq!(stack.len(), i);
        }
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_is_empty<C: Collection<usize>>(mut stack: C) {
        assert!(stack.is_empty());
        for i in 0..5 {
            stack.add(i);
            assert!(!stack.is_empty());
        }
        for i in 0..5 {
            stack.remove();
            assert_eq!(stack.is_empty(), i == 4);
        }
    }

    #[test_collection(Stack, ArrayStack)]
    fn basic_test_stack<C: Collection<usize>>(mut stack: C) {
        for i in 0..10 {
            stack.add(i);
        }
        for mut i in (0..10).rev() {
            assert_eq!(stack.len(), i + 1);
            assert!(!stack.is_empty());

            assert_eq!(stack.peek(), Some(&i));
            assert_eq!(stack.peek_mut(), Some(&mut i));

            match stack.get(1) {
                Some(x) => assert_eq!(*x, i - 1),
                None => assert_eq!(i, 0),
            }
            match stack.get_mut(1) {
                Some(x) => assert_eq!(*x, i - 1),
                None => assert_eq!(i, 0),
            }

            assert_eq!(stack.find(&i), Some(0));
            assert!(stack.contains(&i));

            assert_eq!(stack.remove(), Some(i));
        }

        assert_eq!(stack.len(), 0);
        assert!(stack.is_empty());

        assert_eq!(stack.peek(), None);
        assert_eq!(stack.peek_mut(), None);

        assert_eq!(stack.get(2), None);
        assert_eq!(stack.get_mut(2), None);

        assert_eq!(stack.find(&0), None);
        assert!(!stack.contains(&0));

        assert_eq!(stack.remove(), None);

        for i in 0..10 {
            stack.add(i);
        }
        stack.clear();

        assert_eq!(stack.len(), 0);
        assert!(stack.is_empty());

        assert_eq!(stack.peek(), None);
        assert_eq!(stack.peek_mut(), None);

        assert_eq!(stack.get(2), None);
        assert_eq!(stack.get_mut(2), None);

        assert_eq!(stack.find(&0), None);
        assert!(!stack.contains(&0));

        assert_eq!(stack.remove(), None);
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_into_iter_stack<C: Collection<usize> + Iterators<usize>>(mut stack: C) {
        for i in 0..10_usize {
            stack.add(i);
        }

        for (i, elem) in stack.iter().enumerate() {
            assert_eq!(*elem, 9 - i);
        }
        let mut i = 10_usize;
        for elem in &stack {
            i -= 1;
            assert_eq!(*elem, i);
        }

        for (i, elem) in stack.iter_mut().enumerate() {
            *elem += 1;
            assert_eq!(*elem, 10 - i);
        }
        let mut i = 10_usize;
        for elem in &mut stack {
            *elem -= 1;
            i -= 1;
            assert_eq!(*elem, i);
        }

        for (i, elem) in stack.into_iter().enumerate() {
            assert_eq!(elem, 9 - i);
        }
    }

    #[test_collection(Stack, ArrayStack)]
    fn test_from_iter<C: Collection<usize>>(mut _stack: C) {
        let mut stack: C<usize> = vec![1, 2, 3, 4, 5].into_iter().collect();

        assert_eq!(stack.len(), 5);
        assert!(!stack.is_empty());
        assert_eq!(stack.peek(), Some(&5));

        for i in (1..6).rev() {
            assert_eq!(stack.remove(), Some(i));
        }
    }

    #[test]
    fn test_macro_stack() {
        // No args
        let mut stack = stack![];
        stack.add(1);
        assert_eq!(stack.remove(), Some(1));

        // List of args
        let mut stack = stack![1, 2, 3, 4, 5];
        assert_eq!(stack.len(), 5);
        assert!(!stack.is_empty());
        assert_eq!(stack.peek(), Some(&5));

        for i in (1..6).rev() {
            assert_eq!(stack.remove(), Some(i));
        }

        // Arg and number of args
        let mut stack = stack![1; 5];
        assert_eq!(stack.len(), 5);
        assert!(!stack.is_empty());
        assert_eq!(stack.peek(), Some(&1));

        for _ in 0..5 {
            assert_eq!(stack.remove(), Some(1));
        }
    }

    #[test]
    fn test_macro_array_stack() {
        // No args
        let mut stack = array_stack![];
        stack.add(1);
        assert_eq!(stack.remove(), Some(1));

        // List of args
        let mut stack = array_stack![1, 2, 3, 4, 5];
        assert_eq!(stack.len(), 5);
        assert!(!stack.is_empty());
        assert_eq!(stack.peek(), Some(&5));

        for i in (1..6).rev() {
            assert_eq!(stack.remove(), Some(i));
        }

        // Arg and number of args
        let mut stack = array_stack![1; 5];
        assert_eq!(stack.len(), 5);
        assert!(!stack.is_empty());
        assert_eq!(stack.peek(), Some(&1));

        for _ in 0..5 {
            assert_eq!(stack.remove(), Some(1));
        }
    }
}
