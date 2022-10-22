//! A collection of different implementations of a queue based on the `FIFO` principle. There some
//! structs that implement the [`DequeCollection`] trait, which allows them to be used as both
//! `LIFO` and `FIFO` queues.
//!
//! Currently, the following implementations are available:
//!
//! - **Standard Queue (Pure `FIFO`):**
//!     - [`Queue`]: A linked queue based on nodes.
//!
//! - **Double-ended Queue (`FIFO` and `LIFO`):**
//!     - [`Deque`]: A linked double-ended queue based on nodes.
//!     - [`CircularDeque`]: An array-based double-ended queue based on a circular array.
//!
//! For more information, see the respective structs' documentation.
//!
//! For a pure `LIFO` data structure, see the [`stack`] module.
//! For a priority queue, see the [`priority_queue`] module.
//!
//! [`stack`]: mod@crate::stack
//! [`priority_queue`]: mod@crate::priority_queue
#![warn(missing_docs)]
use crate::collection::{Collection, ExpansionMode, FixedSizeCollection, Iterators};
use std::cmp::Ordering;
use std::marker::PhantomData;
use std::ptr::NonNull;
use trait_based_collection_macros::{internal_check_expansion_add, iterator, All};

/// Trait that encapsulates the common functionality of a double-ended queue. This means that the
/// queue can be used as both a `LIFO` and `FIFO` queue. This trait is a sub-trait of the
/// [`Collection`] trait, allowing to implement some default methods associated with a queue
/// collection ([`push_back`], [`pop_front`], [`peek_front`], [`peek_front_mut`], [`peek_back`],
/// [`peek_back_mut`]).
///
/// # Examples
///
/// A simple example of creating a [`DequeCollection`] by using a wrapper around the [`Vec`] data
/// structure with the minimum amount of code (by using the default implementation of the
/// different methods):
///
/// ```
/// # use trait_based_collection::{prelude::*, macros::{check_expansion_add, All}};
/// #
/// #[derive(All)]
/// struct MyCollection<T> {
///     data: Vec<T>,
/// }
///
/// # impl<'a, T: 'a> Iterators<'a, T> for MyCollection<T> {
/// #     type ItemRef = &'a T;
/// #     type ItemMut = &'a mut T;
/// #
/// #     type Iter = std::slice::Iter<'a, T>;
/// #     type IterMut = std::slice::IterMut<'a, T>;
/// #
/// #     fn iter(&'a self) -> Self::Iter {
/// #         self.data.iter()
/// #     }
/// #
/// #     fn iter_mut(&'a mut self) -> Self::IterMut {
/// #         self.data.iter_mut()
/// #     }
/// # }
/// #
/// # impl<'a, T: 'a> Collection<'a, T> for MyCollection<T> {
/// #     fn new_default() -> Self where Self: Sized {
/// #         MyCollection {
/// #            data: Vec::new(),
/// #         }
/// #     }
/// #
/// #     fn add(&mut self, value: T) {
/// #         self.data.push(value);
/// #     }
/// #
/// #     fn remove(&mut self) -> Option<T> {
/// #         self.data.pop()
/// #     }
/// #
/// #     fn len(&self) -> usize {
/// #         self.data.len()
/// #     }
/// # }
/// #
/// impl<'a, T: 'a> DequeCollection<'a, T> for MyCollection<T> {
///     fn push_front(&mut self, value: T) {
///         self.data.insert(0, value);
///     }
///
///     fn pop_back(&mut self) -> Option<T> {
///         self.data.pop()
///     }
/// }
/// ```
///
/// [`push_back`]: DequeCollection::push_back
/// [`pop_front`]: DequeCollection::pop_front
/// [`peek_front`]: DequeCollection::peek_front
/// [`peek_front_mut`]: DequeCollection::peek_front_mut
/// [`peek_back`]: DequeCollection::peek_back
/// [`peek_back_mut`]: DequeCollection::peek_back_mut
pub trait DequeCollection<'a, T>: Collection<'a, T>
where
    T: 'a,
{
    /// Pushes a new element to the front of the queue.
    ///
    /// # Examples
    ///
    /// Example using [`Deque`]:
    /// ```
    /// use trait_based_collection::{prelude::*, Deque};
    ///
    /// let mut deque: Deque<u32> = Deque::default();
    /// deque.push_front(1);
    /// deque.push_front(2);
    ///
    /// assert_eq!(deque.peek_front(), Some(&2));
    /// assert_eq!(deque.peek_back(), Some(&1));
    /// ```
    fn push_front(&mut self, value: T);

    /// Pushes a new element to the back of the queue. This is the same as [`add`].
    ///
    /// # Examples
    ///
    /// Example using [`CircularDeque`]:
    /// ```
    /// use trait_based_collection::{prelude::*, CircularDeque};
    ///
    /// let mut deque: CircularDeque<u32> = CircularDeque::default();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// assert_eq!(deque.peek_front(), Some(&1));
    /// assert_eq!(deque.peek_back(), Some(&2));
    /// ```
    ///
    /// [`add`]: Collection::add
    fn push_back(&mut self, value: T) {
        self.add(value);
    }

    /// Removes the element from the front of the queue. This is the same as [`remove`].
    ///
    /// # Examples
    ///
    /// Example using [`Deque`]:
    /// ```
    /// use trait_based_collection::{prelude::*, Deque};
    ///
    /// let mut deque: Deque<u32> = Deque::default();
    /// deque.push_front(1);
    /// deque.push_front(2);
    ///
    /// assert_eq!(deque.pop_front(), Some(2));
    /// assert_eq!(deque.pop_front(), Some(1));
    /// assert_eq!(deque.pop_front(), None);
    /// ```
    ///
    /// [`remove`]: Collection::remove
    fn pop_front(&mut self) -> Option<T> {
        self.remove()
    }

    /// Removes the element from the back of the queue.
    ///
    /// # Examples
    ///
    /// Example using [`CircularDeque`]:
    /// ```
    /// use trait_based_collection::{prelude::*, CircularDeque};
    ///
    /// let mut deque: CircularDeque<u32> = CircularDeque::default();
    /// deque.push_front(1);
    /// deque.push_front(2);
    ///
    /// assert_eq!(deque.pop_back(), Some(1));
    /// assert_eq!(deque.pop_back(), Some(2));
    /// assert_eq!(deque.pop_back(), None);
    /// ```
    fn pop_back(&mut self) -> Option<T>;

    /// Returns a reference to the element at the front of the queue. This is the same as [`peek`].
    ///
    /// # Examples
    ///
    /// Example using [`Deque`]:
    /// ```
    /// use trait_based_collection::{prelude::*, Deque};
    ///
    /// let mut deque: Deque<u32> = Deque::default();
    /// assert_eq!(deque.peek_front(), None);
    /// deque.push_front(1);
    /// assert_eq!(deque.peek_front(), Some(&1));
    /// deque.push_front(2);
    /// assert_eq!(deque.peek_front(), Some(&2));
    /// ```
    ///
    /// [`peek`]: Collection::peek
    fn peek_front(&'a self) -> Option<Self::ItemRef> {
        self.peek()
    }

    /// Returns a mutable reference to the element at the front of the queue. This is the same as
    /// [`peek_mut`].
    ///
    /// # Examples
    ///
    /// Example using [`CircularDeque`]:
    /// ```
    /// use trait_based_collection::{prelude::*, CircularDeque};
    ///
    /// let mut deque: CircularDeque<u32> = CircularDeque::default();
    /// assert_eq!(deque.peek_front_mut(), None);
    /// deque.push_front(1);
    /// assert_eq!(deque.peek_front_mut(), Some(&mut 1));
    /// deque.push_front(2);
    /// assert_eq!(deque.peek_front_mut(), Some(&mut 2));
    /// ```
    ///
    /// [`peek_mut`]: Collection::peek_mut
    fn peek_front_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.peek_mut()
    }

    /// Returns a reference to the element at the back of the queue. This is the same as [`get`]
    /// with the index `self.len() - 1`.
    ///
    /// # Examples
    ///
    /// Example using [`Deque`]:
    /// ```
    /// use trait_based_collection::{prelude::*, Deque};
    ///
    /// let mut deque: Deque<u32> = Deque::default();
    /// assert_eq!(deque.peek_back(), None);
    /// deque.push_front(1);
    /// assert_eq!(deque.peek_back(), Some(&1));
    /// deque.push_front(2);
    /// assert_eq!(deque.peek_back(), Some(&1));
    /// ```
    ///
    /// [`get`]: Collection::get
    fn peek_back(&'a self) -> Option<Self::ItemRef> {
        self.get(self.len() - 1)
    }

    /// Returns a mutable reference to the element at the back of the queue. This is the same as
    /// [`get_mut`] with the index `self.len() - 1`.
    ///
    /// # Examples
    /// ```
    /// use trait_based_collection::{prelude::*, CircularDeque};
    ///
    /// let mut deque: CircularDeque<u32> = CircularDeque::default();
    /// assert_eq!(deque.peek_back_mut(), None);
    /// deque.push_front(1);
    /// assert_eq!(deque.peek_back_mut(), Some(&mut 1));
    /// deque.push_front(2);
    /// assert_eq!(deque.peek_back_mut(), Some(&mut 1));
    /// ```
    ///
    /// [`get_mut`]: Collection::get_mut
    fn peek_back_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.get_mut(self.len() - 1)
    }
}

/// A simple-linked node for the basic [`Queue`]. The node contains a value and a pointer to the
/// previous node.
///
/// This struct is not intended to be used directly by the end-user.
#[derive(Debug)]
struct NodeQueue<T> {
    /// The value stored in the node.
    value: T,
    /// The pointer to the previous node.
    prev: Option<NonNull<NodeQueue<T>>>,
}

impl<T> NodeQueue<T> {
    /// Creates a new node with the given value and assigns the previous node to `None`.
    const fn new(value: T) -> Self {
        Self { value, prev: None }
    }
}

/// A queue is a collection that follows the FIFO (first-in-first-out) principle. This means that
/// elements are added to the back of the queue and removed from the front of the queue. This
/// implementation uses a linked-based structure.
///
/// # Examples
/// ```
/// use trait_based_collection::{prelude::*, Queue};
///
/// let mut queue: Queue<u32> = Queue::new_default();
/// queue.add(1);
/// queue.add(2);
/// queue.add(3);
///
/// assert_eq!(queue.peek(), Some(&1));
/// assert_eq!(queue.remove(), Some(1));
/// assert_eq!(queue.remove(), Some(2));
/// assert_eq!(queue.remove(), Some(3));
/// assert_eq!(queue.remove(), None);
/// ```
#[derive(Debug, All)]
pub struct Queue<T> {
    /// The head of the queue.
    head: Option<NonNull<NodeQueue<T>>>,
    /// The tail of the queue.
    tail: Option<NonNull<NodeQueue<T>>>,
    /// The number of elements in the queue.
    len: usize,
}

/// An immutable iterator over the elements of a [`Queue`]. This struct is created by the [`iter`]
/// method on [`Queue`]. See its documentation for more.
///
/// [`iter`]: Queue::iter
pub struct QueueIter<'a, T> {
    /// The current node.
    current: Option<NonNull<NodeQueue<T>>>,
    /// The amount of elements left to iterate over.
    len: usize,
    /// A marker to pin the lifetime of the iterator.
    _marker: PhantomData<&'a T>,
}

impl<'a, T> QueueIter<'a, T> {
    /// Creates a new iterator over the elements of the given a reference to a [`Queue`].
    const fn new(stack: &'a Queue<T>) -> Self {
        QueueIter {
            current: stack.head,
            len: stack.len,
            _marker: PhantomData,
        }
    }
}

iterator!(Queue, QueueIter, ref, {
    let current = self.current.take()?;
    unsafe {
        let current = current.as_ref();
        self.current = current.prev;
        self.len -= 1;
        Some(&current.value)
    }
});

/// A mutable iterator over the elements of a [`Queue`]. This struct is created by the [`iter_mut`]
/// method on [`Queue`]. See its documentation for more.
///
/// [`iter_mut`]: Queue::iter_mut
pub struct QueueIterMut<'a, T> {
    /// The current node.
    current: Option<NonNull<NodeQueue<T>>>,
    /// The amount of elements left to iterate over.
    len: usize,
    /// A marker to pin the lifetime of the iterator.
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> QueueIterMut<'a, T> {
    /// Creates a new iterator over the elements of the given a mutable reference to a [`Queue`].
    fn new(stack: &'a mut Queue<T>) -> Self {
        QueueIterMut {
            current: stack.head,
            len: stack.len,
            _marker: PhantomData,
        }
    }
}

iterator!(Queue, QueueIterMut, mut, {
    let mut current = self.current.take()?;
    unsafe {
        let current = current.as_mut();
        self.current = current.prev;
        self.len -= 1;
        Some(&mut current.value)
    }
});

impl<'a, T> Iterators<'a, T> for Queue<T>
where
    T: 'a,
{
    type ItemRef = &'a T;
    type ItemMut = &'a mut T;

    type Iter = QueueIter<'a, T>;
    type IterMut = QueueIterMut<'a, T>;

    fn iter(&'a self) -> Self::Iter {
        QueueIter::new(self)
    }
    fn iter_mut(&'a mut self) -> Self::IterMut {
        QueueIterMut::new(self)
    }
}

impl<T> Queue<T> {
    /// Returns a reference to the node at the given index if it exists. The index is 0-based. If
    /// the index is out of bounds, `None` is returned.
    ///
    /// This method is used internally by the [`get`] and [`get_mut`] methods.
    ///
    /// [`get`]: Collection::get
    /// [`get_mut`]: Collection::get_mut
    fn get_node(&self, index: usize) -> Option<NonNull<NodeQueue<T>>> {
        if index >= self.len() {
            return None;
        }
        #[allow(clippy::unwrap_used)]
        (0..index).fold(self.head, |node, _| unsafe { node.unwrap().as_ref().prev })
    }
}

impl<'a, T> Collection<'a, T> for Queue<T>
where
    T: 'a,
{
    fn new_default() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    fn add(&mut self, value: T) {
        let node = Box::new(NodeQueue::new(value));
        let node_ptr = NonNull::new(Box::into_raw(node)).expect("Failed to allocate memory");

        if let Some(mut tail) = self.tail {
            unsafe {
                tail.as_mut().prev = Some(node_ptr);
            }
        } else {
            self.head = Some(node_ptr);
        }
        self.len += 1;
        self.tail = Some(node_ptr);
    }

    fn remove(&mut self) -> Option<T> {
        let mut node = self.head.take()?;
        self.len -= 1;

        if self.is_empty() {
            self.tail = None;
        }

        unsafe {
            if let Some(prev) = node.as_mut().prev.take() {
                self.head = Some(prev);
            }

            Some(Box::from_raw(node.as_ptr()).value)
        }
    }

    fn peek(&self) -> Option<Self::ItemRef> {
        self.head.map(|head| unsafe { &head.as_ref().value })
    }

    fn peek_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.head
            .map(|mut head| unsafe { &mut head.as_mut().value })
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

/// A double-linked node for [`Deque`]. The node contains a value and two pointers to the previous
/// and next node.
///
/// This struct is not intended to be used directly by the end-user.
#[derive(Debug)]
struct NodeDeque<T> {
    /// The value stored in the node.
    value: T,
    /// A pointer to the previous node.
    prev: Option<NonNull<NodeDeque<T>>>,
    /// A pointer to the next node.
    next: Option<NonNull<NodeDeque<T>>>,
}

impl<T> NodeDeque<T> {
    /// Creates a new node with the given value.
    const fn new(value: T) -> Self {
        Self {
            value,
            prev: None,
            next: None,
        }
    }
}

/// A double-ended queue. This data structure is a combination of a [`Stack`] and a [`Queue`]. It
/// allows to push and pop elements from both ends of the queue. This data structure implements both
/// LIFO and FIFO. For more information, see the [`DequeCollection`] trait.
///
/// The default behavior for the [`Collection`] trait is to interpret the [`Deque`] as a FIFO queue.
///
/// # Examples
/// ```
/// use trait_based_collection::{prelude::*, Deque};
///
/// let mut deque = Deque::new_default();
/// deque.push_back(1);
/// deque.push_back(2);
/// deque.push_front(3);
///
/// assert_eq!(deque.pop_front(), Some(3));
/// assert_eq!(deque.pop_front(), Some(1));
/// assert_eq!(deque.pop_front(), Some(2));
/// assert_eq!(deque.pop_front(), None);
/// ```
///
/// [`Stack`]: crate::stack::Stack
/// [`DequeCollection`]: DequeCollection
/// [`Collection`]: Collection
#[derive(Debug, All)]
pub struct Deque<T> {
    /// The head of the deque.
    head: Option<NonNull<NodeDeque<T>>>,
    /// The tail of the deque.
    tail: Option<NonNull<NodeDeque<T>>>,
    /// The number of elements in the deque.
    len: usize,
}

impl<T> DoubleEndedIterator for DequeIntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.0.pop_back()
    }
}

/// An immutable iterator over the elements of a [`Deque`]. This struct is created by the [`iter`]
/// method on [`Deque`]. See its documentation for more.
///
/// [`iter`]: Deque::iter
pub struct DequeIter<'a, T> {
    /// Current node in the FIFO walk.
    current_normal: Option<NonNull<NodeDeque<T>>>,
    /// Current node in the LIFO walk.
    current_reversed: Option<NonNull<NodeDeque<T>>>,
    /// The amount of elements left to iterate over.
    len: usize,
    /// A marker to pin the lifetime of the deque.
    _marker: PhantomData<&'a T>,
}

impl<'a, T> DequeIter<'a, T> {
    /// Creates a new iterator over the elements of the given a reference to a [`Deque`].
    const fn new(stack: &'a Deque<T>) -> Self {
        DequeIter {
            current_normal: stack.head,
            current_reversed: stack.tail,
            len: stack.len,
            _marker: PhantomData,
        }
    }
}

iterator!(Deque, DequeIter, ref, {
    if self.len == 0 {
        return None;
    }
    let current = self.current_normal.take()?;

    unsafe {
        let current = current.as_ref();
        self.current_normal = current.prev;
        self.len -= 1;
        Some(&current.value)
    }
});

impl<'a, T> DoubleEndedIterator for DequeIter<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            return None;
        }
        let current = self.current_reversed.take()?;

        unsafe {
            let current = current.as_ref();
            self.current_reversed = current.next;
            self.len -= 1;
            Some(&current.value)
        }
    }
}

/// A mutable iterator over the elements of a [`Deque`]. This struct is created by the [`iter_mut`]
/// method on [`Deque`]. See its documentation for more.
///
/// [`iter_mut`]: Deque::iter_mut
pub struct DequeIterMut<'a, T> {
    /// Current node in the FIFO walk.
    current_normal: Option<NonNull<NodeDeque<T>>>,
    /// Current node in the LIFO walk.
    current_reversed: Option<NonNull<NodeDeque<T>>>,
    /// The amount of elements left to iterate over.
    len: usize,
    /// A marker to pin the lifetime of the deque.
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> DequeIterMut<'a, T> {
    /// Creates a new iterator over the elements of the given a reference to a [`Deque`].
    fn new(stack: &'a mut Deque<T>) -> Self {
        DequeIterMut {
            current_normal: stack.head,
            current_reversed: stack.tail,
            len: stack.len,
            _marker: PhantomData,
        }
    }
}

iterator!(Deque, DequeIterMut, mut, {
    if self.len == 0 {
        return None;
    }
    let mut current = self.current_normal.take()?;

    unsafe {
        let current = current.as_mut();
        self.current_normal = current.prev;
        self.len -= 1;
        Some(&mut current.value)
    }
});

impl<'a, T> DoubleEndedIterator for DequeIterMut<'a, T> {
    fn next_back(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            return None;
        }
        let mut current = self.current_reversed.take()?;

        unsafe {
            let current = current.as_mut();
            self.current_reversed = current.next;
            self.len -= 1;
            Some(&mut current.value)
        }
    }
}

impl<'a, T> Iterators<'a, T> for Deque<T>
where
    T: 'a,
{
    type ItemRef = &'a T;
    type ItemMut = &'a mut T;

    type Iter = DequeIter<'a, T>;
    type IterMut = DequeIterMut<'a, T>;

    fn iter(&'a self) -> Self::Iter {
        DequeIter::new(self)
    }

    fn iter_mut(&'a mut self) -> Self::IterMut {
        DequeIterMut::new(self)
    }
}

impl<T> Deque<T> {
    /// Returns a reference to the node at the given index if it exists. The index is 0-based. If
    /// the index is out of bounds, `None` is returned. Also, it will start from the head or the
    /// tail depending on which one is closer to the given index, so it is not guaranteed that the
    /// node will be found in `O(n/2)` time.
    ///
    /// This method is used internally by the [`get`] and [`get_mut`] methods.
    ///
    /// [`get`]: Deque::get
    /// [`get_mut`]: Deque::get_mut
    fn get_node(&self, index: usize) -> Option<NonNull<NodeDeque<T>>> {
        if index >= self.len() {
            return None;
        }
        #[allow(clippy::unwrap_used)] // Index is valid
        if index <= self.len / 2 {
            (0..index).fold(self.head, |node, _| unsafe { node.unwrap().as_ref().prev })
        } else {
            (index + 1..self.len())
                .fold(self.tail, |node, _| unsafe { node.unwrap().as_ref().next })
        }
    }
}

impl<'a, T> Collection<'a, T> for Deque<T>
where
    T: 'a,
{
    fn new_default() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    fn add(&mut self, value: T) {
        let node = Box::new(NodeDeque::new(value));
        let mut node_ptr = NonNull::new(Box::into_raw(node)).expect("Failed to allocate memory");

        if let Some(mut tail_ptr) = self.tail {
            unsafe {
                node_ptr.as_mut().next = Some(tail_ptr);
                tail_ptr.as_mut().prev = Some(node_ptr);
            }
        } else {
            self.head = Some(node_ptr);
        }
        self.len += 1;
        self.tail = Some(node_ptr);
    }

    fn remove(&mut self) -> Option<T> {
        let mut node = self.head.take()?;
        self.len -= 1;

        if self.is_empty() {
            self.tail = None;
        }

        unsafe {
            if let Some(mut prev) = node.as_mut().prev.take() {
                prev.as_mut().next = None;
                self.head = Some(prev);
            }

            Some(Box::from_raw(node.as_ptr()).value)
        }
    }

    fn peek(&self) -> Option<Self::ItemRef> {
        self.head.map(|head| unsafe { &head.as_ref().value })
    }

    fn peek_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.head
            .map(|mut head| unsafe { &mut head.as_mut().value })
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

impl<'a, T> DequeCollection<'a, T> for Deque<T>
where
    T: 'a,
{
    fn push_front(&mut self, value: T) {
        let node = Box::new(NodeDeque::new(value));
        let mut node_ptr = NonNull::new(Box::into_raw(node)).expect("Failed to allocate memory");

        if let Some(mut head_ptr) = self.head {
            unsafe {
                node_ptr.as_mut().prev = Some(head_ptr);
                head_ptr.as_mut().next = Some(node_ptr);
            }
        } else {
            self.tail = Some(node_ptr);
        }
        self.len += 1;
        self.head = Some(node_ptr);
    }

    fn pop_back(&mut self) -> Option<T> {
        let mut node = self.tail.take()?;
        self.len -= 1;

        if self.is_empty() {
            self.head = None;
        }

        unsafe {
            if let Some(mut next) = node.as_mut().next.take() {
                next.as_mut().prev = None;
                self.tail = Some(next);
            }

            Some(Box::from_raw(node.as_ptr()).value)
        }
    }

    fn peek_back(&self) -> Option<Self::ItemRef> {
        self.tail.map(|tail| unsafe { &(*tail.as_ref()).value })
    }

    fn peek_back_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.tail
            .map(|mut tail| unsafe { &mut (*tail.as_mut()).value })
    }
}

/// A circular deque capable of expanding its capacity when needed. It is implemented using [`Vec`],
/// so the elements are stored contiguously in memory. The main difference between this and a
/// [`Deque`] is that this one does not use nodes. This data structure implements both LIFO and
/// FIFO.
///
/// Depending on the expansion mode, once the capacity is reached, the deque will behave differently
/// depending on the mode. For more information, see the [`ExpansionMode`] documentation.
///
/// # Examples
/// ```
/// use trait_based_collection::{prelude::*, CircularDeque};
///
/// let mut deque = CircularDeque::with_mode(2, ExpansionMode::Ignore);
/// deque.add(1);
/// deque.add(2);
/// deque.add(3);
///
/// assert_eq!(deque.len(), 2);
/// assert_eq!(deque.remove(), Some(1));
/// assert_eq!(deque.remove(), Some(2));
/// assert_eq!(deque.remove(), None);
/// ```
///
/// [`ExpansionMode`]: crate::collection::ExpansionMode
#[derive(Debug, All)]
pub struct CircularDeque<T> {
    /// A vector with the size of the capacity of the deque where the elements are stored.
    data: Vec<Option<T>>,

    /// The index of the first element in the deque.
    head: usize,
    /// The index of the last element in the deque.
    tail: usize,

    /// The number of elements in the deque.
    len: usize,
    /// The current mode of expansion of the deque that determinate the behaviour the collection is
    /// full. See [`ExpansionMode`] for more information.
    ///
    /// [`ExpansionMode`]: crate::collection::ExpansionMode
    pub mode: ExpansionMode,
}

impl<T> DoubleEndedIterator for CircularDequeIntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.0.pop_back()
    }
}

/// An immutable iterator over the elements of a [`CircularDeque`]. This struct is created by the
/// [`iter`] method on [`CircularDeque`]. See its documentation for more.
///
/// [`iter`]: CircularDeque::iter
pub struct CircularDequeIter<'a, T> {
    /// The deque that is being iterated.
    deque: &'a CircularDeque<T>,
    /// The current index of the iterator in FIFO order.
    current_normal: usize,
    /// The current index of the iterator in LIFO order.
    current_reversed: usize,
    /// The amount of elements left to iterate over.
    len: usize,
}

impl<'a, T> CircularDequeIter<'a, T> {
    /// Creates a new iterator over the elements of the given a reference to a [`CircularDeque`].
    const fn new(deque: &'a CircularDeque<T>) -> Self {
        CircularDequeIter {
            deque,
            current_normal: deque.head,
            current_reversed: deque.tail,
            len: deque.len,
        }
    }
}

iterator!(CircularDeque, CircularDequeIter, ref, {
    if self.len == 0 {
        return None;
    }
    let current = self.current_normal;

    self.current_normal = self.deque.sub_index(current, 1);
    self.len -= 1;
    self.deque.data[current].as_ref()
});

impl<'a, T> DoubleEndedIterator for CircularDequeIter<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            return None;
        }
        let current = self.current_reversed;

        self.current_reversed = self.deque.add_index(current, 1);
        self.len -= 1;
        self.deque.data[current].as_ref()
    }
}

/// A mutable iterator over the elements of a [`CircularDeque`]. This struct is created by the
/// [`iter_mut`] method on [`CircularDeque`]. See its documentation for more.
///
/// [`iter_mut`]: CircularDeque::iter_mut
pub struct CircularDequeIterMut<'a, T> {
    /// The deque that is being iterated.
    deque: &'a mut CircularDeque<T>,
    /// The current index of the iterator in FIFO order.
    current_normal: usize,
    /// The current index of the iterator in LIFO order.
    current_reversed: usize,
    /// The amount of elements left to iterate over.
    len: usize,
}

impl<'a, T> CircularDequeIterMut<'a, T> {
    /// Creates a new iterator over the elements of the given a reference to a [`CircularDeque`].
    fn new(deque: &'a mut CircularDeque<T>) -> Self {
        CircularDequeIterMut {
            current_normal: deque.head,
            current_reversed: deque.tail,
            len: deque.len,
            deque,
        }
    }
}

iterator!(CircularDeque, CircularDequeIterMut, mut, {
    if self.len == 0 {
        return None;
    }
    let current = self.current_normal;

    self.current_normal = self.deque.sub_index(current, 1);
    let current_ptr = self.deque.data[current].as_mut()?;
    self.len -= 1;
    // Avoids compiler error on reference duration.
    unsafe { Some(&mut *(current_ptr as *mut T)) }
});

impl<'a, T> DoubleEndedIterator for CircularDequeIterMut<'a, T> {
    fn next_back(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            return None;
        }
        let current = self.current_reversed;

        self.current_reversed = (current + 1) % self.deque.capacity();
        let current_ptr = self.deque.data[current].as_mut()?;
        self.len -= 1;
        // Avoids compiler error on reference duration.
        unsafe { Some(&mut *(current_ptr as *mut T)) }
    }
}

impl<'a, T> Iterators<'a, T> for CircularDeque<T>
where
    T: 'a,
{
    type ItemRef = &'a T;
    type ItemMut = &'a mut T;

    type Iter = CircularDequeIter<'a, T>;
    type IterMut = CircularDequeIterMut<'a, T>;

    fn iter(&'a self) -> Self::Iter {
        CircularDequeIter::new(self)
    }
    fn iter_mut(&'a mut self) -> Self::IterMut {
        CircularDequeIterMut::new(self)
    }
}

impl<T> CircularDeque<T> {
    fn add_index(&self, index: usize, add: usize) -> usize {
        if self.capacity() == 0 {
            return usize::MAX;
        }
        index.wrapping_add(add) % self.capacity()
    }

    fn sub_index(&self, index: usize, sub: usize) -> usize {
        if self.capacity() == 0 {
            return usize::MAX;
        }
        match index.cmp(&sub) {
            Ordering::Greater => (index - sub) % self.capacity(),
            Ordering::Equal => 0,
            Ordering::Less => self.capacity() - (sub - index) % self.capacity(),
        }
    }
}

impl<'a, T> Collection<'a, T> for CircularDeque<T>
where
    T: 'a,
{
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
        if !self.is_empty() {
            self.tail = self.sub_index(self.tail, 1);
        }
        self.data[self.tail] = Some(value);
        self.len += 1;
    }

    fn remove(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let value = self.data[self.head].take();
        if self.len > 1 {
            self.head = self.sub_index(self.head, 1);
        }

        self.len -= 1;
        value
    }

    fn clear(&mut self) {
        self.data.clear();
        self.head = 0;
        self.tail = 0;
        self.len = 0;
    }

    fn peek(&'a self) -> Option<Self::ItemRef> {
        self.data.get(self.head).map(Option::as_ref)?
    }

    fn peek_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.data.get_mut(self.head).and_then(Option::as_mut)
    }

    fn get(&'a self, index: usize) -> Option<Self::ItemRef> {
        self.data
            .get(self.sub_index(self.head, index))
            .and_then(Option::as_ref)
    }

    fn get_mut(&'a mut self, index: usize) -> Option<Self::ItemMut> {
        let index = self.sub_index(self.head, index);
        self.data.get_mut(index).map(Option::as_mut)?
    }

    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> FixedSizeCollection<'a, T> for CircularDeque<T>
where
    T: 'a,
{
    fn with_mode(capacity: usize, mode: ExpansionMode) -> Self {
        assert_ne!(capacity, 0, "Capacity must be greater than 0");
        Self {
            data: (0..capacity).map(|_| None).collect(),
            head: 0,
            tail: 0,
            len: 0,
            mode,
        }
    }

    fn capacity(&self) -> usize {
        self.data.len()
    }

    fn expand(&mut self, extra_size: usize) {
        let prev_capacity = self.capacity();
        self.data.resize_with(prev_capacity + extra_size, || None);

        if self.tail > self.head {
            for i in self.tail..prev_capacity {
                self.data[extra_size + i] = self.data[i].take();
            }
            self.tail += extra_size;
        }
    }

    fn mode(&self) -> &ExpansionMode {
        &self.mode
    }
}

impl<'a, T> DequeCollection<'a, T> for CircularDeque<T>
where
    T: 'a,
{
    #[internal_check_expansion_add]
    fn push_front(&mut self, value: T) {
        if !self.is_empty() {
            self.head = self.add_index(self.head, 1);
        }
        self.data[self.head] = Some(value);
        self.len += 1;
    }

    fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let value = self.data[self.tail].take();
        if self.len > 1 {
            self.tail = self.add_index(self.tail, 1);
        }

        self.len -= 1;
        value
    }

    fn peek_back(&'a self) -> Option<Self::ItemRef> {
        self.data.get(self.tail).map(Option::as_ref)?
    }

    fn peek_back_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.data.get_mut(self.tail).and_then(Option::as_mut)
    }
}

#[cfg(test)]
mod tests_collection {
    #![allow(clippy::cast_possible_truncation)]
    use super::*;
    use trait_based_collection_macros::test_collection;

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_add<C: Collection<u32>>(mut queue: C) {
        for i in 0..5 {
            queue.add(i);
        }
        queue.add(u32::MAX);
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_remove<C: Collection<u32>>(mut queue: C) {
        for i in 0..5 {
            queue.add(i);
        }
        for i in 0..5 {
            assert_eq!(queue.remove(), Some(i));
        }
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_clear<C: Collection<u32>>(mut queue: C) {
        for i in 0..5 {
            queue.add(i);
        }
        queue.clear();

        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());
        assert_eq!(queue.peek(), None);
        assert_eq!(queue.remove(), None);
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_peek<C: Collection<u32>>(mut queue: C) {
        assert_eq!(queue.peek(), None);
        for i in 0..5 {
            queue.add(i);
            assert_eq!(queue.peek(), Some(&0));
        }
        for i in 0..5 {
            assert_eq!(queue.peek(), Some(&i));
            queue.remove();
        }
        assert_eq!(queue.peek(), None);
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_peek_mut<C: Collection<u32>>(mut queue: C) {
        assert_eq!(queue.peek_mut(), None);
        for i in 0..5 {
            queue.add(i);
            let peek = queue.peek_mut().unwrap();
            assert_eq!(*peek, i);
            *peek += 1;
        }
        assert_eq!(queue.peek_mut(), Some(&mut 5));
        queue.remove();
        for mut i in 1..5 {
            assert_eq!(queue.peek_mut(), Some(&mut i));
            queue.remove();
        }
        assert_eq!(queue.peek_mut(), None);
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_get<C: Collection<u32>>(mut queue: C) {
        for i in 0..5 {
            queue.add(i);
        }
        for i in 0..5 {
            assert_eq!(queue.get(i as usize), Some(&i));
        }
        assert_eq!(queue.get(6), None);
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_get_mut<C: Collection<u32>>(mut queue: C) {
        for i in 0..5 {
            queue.add(i);
        }
        for i in 0..5 {
            let get = queue.get_mut(i as usize).unwrap();
            *get += 1;
            assert_eq!(*get, i + 1);
        }
        assert_eq!(queue.get_mut(6), None);

        for i in 1..6 {
            assert_eq!(queue.remove(), Some(i));
        }
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_find<C: Collection<u32>>(mut queue: C) {
        for i in 0..5 {
            queue.add(i);
        }
        for i in 0..5 {
            assert_eq!(queue.find(&i), Some(i as usize));
        }
        assert_eq!(queue.find(&6), None);
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_contains<C: Collection<u32>>(mut queue: C) {
        for i in 0..5 {
            queue.add(i);
        }
        for i in 0..5 {
            assert!(queue.contains(&i));
        }
        assert!(!queue.contains(&6));
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_len<C: Collection<u32>>(mut queue: C) {
        assert_eq!(queue.len(), 0);
        for i in 0..5 {
            queue.add(i);
            assert_eq!(queue.len(), (i + 1) as usize);
        }
        assert_eq!(queue.len(), 5);
        for i in (0..5_usize).rev() {
            queue.remove();
            assert_eq!(queue.len(), i);
        }
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_is_empty<C: Collection<u32>>(mut queue: C) {
        assert!(queue.is_empty());
        for i in 0..5 {
            queue.add(i);
            assert!(!queue.is_empty());
        }
        for i in 0..5 {
            queue.remove();
            assert_eq!(queue.is_empty(), i == 4);
        }
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn basic_test_queue<C: Collection<u32>>(mut queue: C) {
        for i in 0..10 {
            queue.add(i);
        }
        for mut i in 0..10_u32 {
            assert_eq!(queue.len(), 10 - i as usize);
            assert!(!queue.is_empty());

            assert_eq!(queue.peek(), Some(&i));
            assert_eq!(queue.peek_mut(), Some(&mut i));

            match queue.get(1) {
                Some(x) => assert_eq!(*x, i + 1),
                None => assert_eq!(i, 9),
            }
            match queue.get_mut(1) {
                Some(x) => assert_eq!(*x, i + 1),
                None => assert_eq!(i, 9),
            }

            assert_eq!(queue.find(&i), Some(0));
            assert!(queue.contains(&i));

            assert_eq!(queue.remove(), Some(i));
        }

        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());

        assert_eq!(queue.peek(), None);
        assert_eq!(queue.peek_mut(), None);

        assert_eq!(queue.get(2), None);
        assert_eq!(queue.get_mut(2), None);

        assert_eq!(queue.find(&0), None);
        assert!(!queue.contains(&0));

        assert_eq!(queue.remove(), None);

        for i in 0..10 {
            queue.add(i);
        }
        queue.clear();

        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());

        assert_eq!(queue.peek(), None);
        assert_eq!(queue.peek_mut(), None);

        assert_eq!(queue.get(2), None);
        assert_eq!(queue.get_mut(2), None);

        assert_eq!(queue.find(&0), None);
        assert!(!queue.contains(&0));

        assert_eq!(queue.remove(), None);
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_from_iter<C: Collection<usize>>(mut _queue: C) {
        let mut queue: C<usize> = vec![1, 2, 3, 4, 5].into_iter().collect();

        assert_eq!(queue.len(), 5);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&1));

        for i in 1..6 {
            assert_eq!(queue.remove(), Some(i));
        }
    }

    #[test_collection(Queue, Deque, CircularDeque)]
    fn test_into_iter<C: Collection<u32>>(mut queue: C) {
        for i in 0..5 {
            queue.add(i);
        }

        for (i, &elem) in queue.iter().enumerate() {
            assert_eq!(elem, i as u32);
        }
        let mut i: u32 = 0;
        for elem in &queue {
            assert_eq!(*elem, i);
            i += 1;
        }

        for (i, elem) in queue.iter_mut().enumerate() {
            *elem += 1;
            assert_eq!(*elem, i as u32 + 1);
        }
        let mut i: u32 = 0;
        for elem in &mut queue {
            *elem -= 1;
            assert_eq!(*elem, i);
            i += 1;
        }

        for (i, elem) in queue.into_iter().enumerate() {
            assert_eq!(elem, i as u32);
        }
    }

    #[test]
    fn test_macro_queue() {
        // No args
        let mut queue = queue![];
        queue.add(1);
        assert_eq!(queue.remove(), Some(1));

        // List of args
        let mut queue = queue![1, 2, 3, 4, 5];
        assert_eq!(queue.len(), 5);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&1));

        for i in 1..6 {
            assert_eq!(queue.remove(), Some(i));
        }

        // Arg and number of args
        let mut queue = queue![1; 5];
        assert_eq!(queue.len(), 5);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&1));

        for _ in 0..5 {
            assert_eq!(queue.remove(), Some(1));
        }
    }

    #[test]
    fn test_macro_deque() {
        // No args
        let mut queue = deque![];
        queue.add(1);
        assert_eq!(queue.remove(), Some(1));

        // List of args
        let mut queue = deque![1, 2, 3, 4, 5];
        assert_eq!(queue.len(), 5);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&1));

        for i in 1..6 {
            assert_eq!(queue.remove(), Some(i));
        }

        // Arg and number of args
        let mut queue = deque![1; 5];
        assert_eq!(queue.len(), 5);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&1));

        for _ in 0..5 {
            assert_eq!(queue.remove(), Some(1));
        }
    }

    #[test]
    fn test_cycles_circular_queue() {
        let mut queue = CircularDeque::with_mode(5, ExpansionMode::Panic);
        for _ in 0..10 {
            for i in 0..3 {
                queue.add(i);
            }
            for i in 0..3 {
                assert_eq!(queue.remove(), Some(i));
            }
        }
    }

    #[test]
    fn test_capacity_circular_queue() {
        let mut queue = CircularDeque::with_mode(5, ExpansionMode::Panic);
        assert_eq!(queue.capacity(), 5);
        for _ in 0..7 {
            for i in 0..3 {
                queue.add(i);
                assert_eq!(queue.capacity(), 5);
            }
            for i in 0..3 {
                assert_eq!(queue.remove(), Some(i));
                assert_eq!(queue.capacity(), 5);
            }
        }
    }

    #[test]
    fn test_macro_circular_queue() {
        // No args
        let mut queue = circular_deque![];
        for i in 0..10 {
            queue.add(i);
        }
        assert_eq!(queue.remove(), Some(0));

        // List of args
        let mut queue = circular_deque![1, 2, 3, 4, 5];
        assert_eq!(queue.len(), 5);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&1));

        for i in 1..6 {
            assert_eq!(queue.remove(), Some(i));
        }

        // Arg and number of args
        let mut queue = circular_deque![1; 5];
        assert_eq!(queue.len(), 5);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&1));

        for _ in 0..5 {
            assert_eq!(queue.remove(), Some(1));
        }
    }

    #[test]
    fn test_deque_to_circular_queue() {
        let queue = deque![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
            .into_iter()
            .collect::<CircularDeque<u32>>();
        assert_eq!(queue.len(), 10);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&0));
    }
}

#[cfg(test)]
mod tests_deque_collection {
    use super::*;
    use trait_based_collection_macros::test_collection;

    #[test_collection(Deque, CircularDeque)]
    fn test_push_back<C: Collection<u32>>(mut queue: C) {
        queue.add(1); // Chis is a push_back
        queue.add(2); // Chis is a push_back
        queue.push_back(3);

        // Expected standard exit order: 1, 2, 3

        assert_eq!(queue.len(), 3);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&1));

        assert_eq!(queue.remove(), Some(1));
        assert_eq!(queue.remove(), Some(2));
        assert_eq!(queue.remove(), Some(3));
    }

    #[test_collection(Deque, CircularDeque)]
    fn test_push_front_deque<C: Collection<u32>>(mut queue: C) {
        queue.add(1); // Chis is a push_back
        queue.add(2); // Chis is a push_back
        queue.push_front(3);

        // Expected standard exit order: 3, 1, 2

        assert_eq!(queue.len(), 3);
        assert!(!queue.is_empty());
        assert_eq!(queue.peek(), Some(&3));

        assert_eq!(queue.remove(), Some(3));
        assert_eq!(queue.remove(), Some(1));
        assert_eq!(queue.remove(), Some(2));
    }

    #[test_collection(Deque, CircularDeque)]
    fn test_pop_back_deque<C: Collection<u32>>(mut queue: C) {
        queue.add(1);
        queue.add(2);
        queue.add(3);

        // Expected standard exit order: 1, 2, 3

        assert_eq!(queue.pop_back(), Some(3));
        assert_eq!(queue.pop_back(), Some(2));
        assert_eq!(queue.pop_back(), Some(1));
    }

    #[test_collection(Deque, CircularDeque)]
    fn test_pop_front_deque<C: Collection<u32>>(mut queue: C) {
        queue.add(1);
        queue.add(2);
        queue.add(3);

        // Expected standard exit order: 1, 2, 3

        assert_eq!(queue.pop_front(), Some(1));
        assert_eq!(queue.pop_front(), Some(2));
        assert_eq!(queue.pop_front(), Some(3));
    }

    #[test_collection(Deque, CircularDeque)]
    fn test_peek_front_deque<C: Collection<u32>>(mut queue: C) {
        queue.add(1);
        queue.add(2);
        queue.add(3);

        // Expected standard exit order: 1, 2, 3

        for i in 1..4 {
            assert_eq!(queue.peek_front(), Some(&i));
            queue.remove();
        }
    }

    #[test_collection(Deque, CircularDeque)]
    fn test_peek_back_deque<C: Collection<u32>>(mut queue: C) {
        queue.add(1);
        queue.add(2);
        queue.add(3);

        // Expected standard exit order: 1, 2, 3

        for _ in 1..4 {
            assert_eq!(queue.peek_back(), Some(&3));
            queue.remove();
        }
    }
}
