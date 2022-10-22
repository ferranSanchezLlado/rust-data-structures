//! Traits, helpers, and type definitions for the collection framework.
//!
//! This module contains various tools for interacting with the collections. In summary:
//!
//! - [`Iterators`] is a trait that encapsulates all possible methods for iterating over a
//! [`Collection`].
//! - [`Collection`] is the base trait all collections must implement. Defines a series of methods
//! commonly used by almost all collections.
//! - [`FixedSizeCollection`] is a trait that extends [`Collection`] and adds the ability to define
//! collections with a fixed capacity and the possibility of expanding them. It is mainly intended
//! for collections based on arrays.
//! - [`ExpansionMode`] is a type that defines the behavior of a collection when it is full.
//! - [`check_expansion`] is a function that checks if the collection is full and if it is, expands
//! it depending on the [`ExpansionMode`]. Instead of using this function directly, the
//! [`check_expansion_add`] macro is available to wrap the behavior of a function.
//!
//! For more details, see the respective documentation of each item in the lists.
//!
//! [`check_expansion_add`]: trait_based_collection_macros::check_expansion_add
#![warn(missing_docs)]
use std::ops::{Deref, DerefMut};
pub use trait_based_collection_macros::check_expansion_add;

/// Trait that allows to implement all possible iterators over a [`Collection`]. All collections
/// must implement all iterators, allowing for default implementations across collections.
///
/// There are three different types of iterators:
///
/// - [`iter`] returns an immutable iterator over [`ItemRef`] in the [`Collection`] without
/// consuming them.
/// - [`iter_mut`] returns a mutable iterator over the [`ItemMut`] in the [`Collection`] without
/// consuming them.
/// - [`into_iter`] returns an iterator over the items in the [`Collection`] and consumes the
/// collection .
///
/// # Safety
///
/// All iterators must return the items in the same order as the other iterators. This is
/// required to ensure that the iterators are consistent with each other. This is not checked
/// by the compiler. If this is not upheld, the behavior of the [`Collection`] is undefined.
///
/// [`iter`]: Iterators::iter
/// [`ItemRef`]: Iterators::ItemRef
/// [`iter_mut`]: Iterators::iter_mut
/// [`ItemMut`]: Iterators::ItemMut
/// [`into_iter`]: IntoIterator::into_iter
pub trait Iterators<'a, T>: IntoIterator<Item = T> {
    /// The type of reference the immutable iterator ([`Iter`]) iterates over the items in the
    /// [`Collection`]. The reference is only valid for the duration of the iteration.
    ///
    /// [`Iter`]: Iterators::Iter
    type ItemRef: 'a + Deref<Target = T>;

    /// The type of mutable reference the mutable iterator ([`IterMut`]) iterates over the items in
    /// the [`Collection`]. The reference is only valid for the duration of the iteration.
    ///
    /// [`IterMut`]: Iterators::IterMut
    type ItemMut: 'a + DerefMut<Target = T>;

    /// Which kind of iterator is returned by [`iter`].
    ///
    /// [`iter`]: Iterators::iter
    type Iter: Iterator<Item = Self::ItemRef>;
    /// Which kind of iterator is returned by [`iter_mut`].
    ///
    /// [`iter_mut`]: Iterators::iter_mut
    type IterMut: Iterator<Item = Self::ItemMut>;

    /// Creates an immutable iterator over the items in the [`Collection`] without consuming them.
    ///
    /// If you want to be able to modify the collection , you should use the [`iter_mut`] method.
    /// If you want to consume the collection , you should use the [`into_iter`] method that is
    /// implemented deriving the [`IntoIterator`](trait_based_collection_macros::IntoIterator) trait.
    ///
    /// Also, it is recommended to implement the [`IntoIterator`] trait but through reference, like
    /// this example based on the one at collection :
    ///
    /// # Examples
    ///
    /// Example using the [`ArrayStack`]:
    ///
    /// ```
    /// use trait_based_collection::{ArrayStack, prelude::*};
    ///
    /// let mut collection = ArrayStack::with_capacity(10);
    /// for i in 0..10 {
    ///     collection.add(i);
    /// }
    /// for item in collection.iter() {
    ///     println!("{}", item);
    /// }
    /// ```
    ///
    /// Example if the `IntoIterator` is implemented through reference:
    ///
    /// ```
    /// use trait_based_collection::{ArrayStack, prelude::*};
    ///
    /// let mut collection = ArrayStack::with_capacity(10);
    /// for i in 0..10 {
    ///     collection.add(i);
    /// }
    /// for item in &collection {
    ///     println!("{}", item);
    /// }
    /// ```
    ///
    /// [`iter_mut`]: Iterators::iter_mut
    /// [`into_iter`]: IntoIterator::into_iter
    /// [`ArrayStack`]: crate::stack::ArrayStack
    fn iter(&'a self) -> Self::Iter;

    /// Creates a mutable iterator over the items in the [`Collection`] without consuming them.
    ///
    /// If you don't want to be able to modify the collection , you should use the [`iter`] method.
    /// If you want to consume the collection , you should use the [`into_iter`] method that is
    /// implemented deriving the [`IntoIterator`](trait_based_collection_macros::IntoIterator) trait.
    ///
    /// Also, it is recommended to implement the [`IntoIterator`] trait but through reference, like
    /// this example based on the one at collection :
    ///
    /// # Examples
    ///
    /// Example using the [`ArrayStack`]:
    ///
    /// ```
    /// use trait_based_collection::{ArrayStack, prelude::*};
    ///
    /// let mut collection = ArrayStack::with_capacity(10);
    /// for i in 0..10 {
    ///     collection.add(i);
    /// }
    /// for item in collection.iter_mut() {
    ///     println!("{}", item);
    /// }
    /// ```
    ///
    /// Example if the `IntoIterator` is implemented through reference:
    ///
    /// ```
    /// use trait_based_collection::{ArrayStack, prelude::*};
    ///
    /// let mut collection = ArrayStack::with_capacity(10);
    /// for i in 0..10 {
    ///     collection.add(i);
    /// }
    /// for item in &collection {
    ///     println!("{}", item);
    /// }
    /// ```
    ///
    /// [`iter`]: Iterators::iter
    /// [`into_iter`]: IntoIterator::into_iter
    /// [`ArrayStack`]: crate::stack::ArrayStack
    fn iter_mut(&'a mut self) -> Self::IterMut;
}

/// This is the trait that all implementations of a collection must implement. A [`Collection`] is a
/// data structure that can be used to store a collection of items.
///
/// The [`Collection`] is generic over any type without the need of any extra traits. This allows
/// the user to create a collection of any type that they want.
///
/// The trait provides a number of methods that can be used to create, manipulate, and retrieve
/// items from the [`Collection`]. The methods are divided into three groups:
///
/// - **Creation:** These methods are used to create a new [`Collection`] and add items to it.
/// There are the following methods:
///     - [`new_default`]: Creates a new [`Collection`] with a default capacity. Normally, this
///     means that the collection will be expandable.
///     - [`with_capacity`]: Creates a new [`Collection`] with a specific capacity. This method is
///     useful if you want to avoid the expense of resizing the collection when adding items.
///     - [`with_approximate_capacity`]: Creates a new [`Collection`] with a capacity that is close
///     to the specified capacity but could be larger. This method is useful if you want to avoid
///     some of the expense of resizing the collection when adding items.
///
/// For more information about capacity, see the trait [`FixedSizeCollection`] which is used to
/// create collections with a fixed capacity (i.e. the collection will not be easily expandable).
///
/// - **Manipulation:** These methods are used to add, remove, and retrieve items from the
/// [`Collection`]. There are the following methods:
///     - [`add`]: Adds an item to the [`Collection`].
///     - [`remove`]: Removes an item from the [`Collection`] and returns the ownership of the item.
///     - [`clear`]: Removes all items from the [`Collection`].
///
/// - **Retrieval:** These methods are used to retrieve items or information from the
/// [`Collection`]. There are the following methods:
///     - [`peek`]: Returns a [`ItemRef`] to the an item in the [`Collection`]. The item should be
///     the same as the one returned by [`remove`].
///     - [`peek_mut`]: Returns a [`ItemMut`] to the an item in the [`Collection`]. The item should
///     be the same as the one returned by [`remove`].
///     - [`get`]: Returns a [`ItemRef`] to the an item at the specified index in the
///     [`Collection`].
///     - [`get_mut`]: Returns a [`ItemMut`] to the an item at the specified index in the
///     [`Collection`].
///     - [`find`]: Returns an index to the an item in the [`Collection`] that matches the
///     specified item.
///     - [`contains`]: Returns true if the [`Collection`] contains the specified item.
///     - [`len`]: Returns the number of items in the [`Collection`].
///     - [`is_empty`]: Returns `true` if the [`Collection`] is empty.
///
/// As briefly mentioned above, the [`Collection`] is intended for all types of data structures.
/// However, if the the amount of items in the collection is known, it is possible to create a
/// [`FixedSizeCollection`] which can be used to create a collection with a fixed capacity. This is
/// mainly for implementation of data structures using arrays.
///
/// # Examples
///
/// A simple example of creating a [`Collection`] by using a wrapper around the [`Vec`] data
/// structure with the minimum amount of code (by using the default implementation of the
/// different methods):
///
/// ```
/// use trait_based_collection::{prelude::*, macros::All};
///
/// #[derive(All)]
/// struct MyCollection<T> {
///     data: Vec<T>,
/// }
///
/// impl<'a, T: 'a> Iterators<'a, T> for MyCollection<T> {
///     type ItemRef = &'a T;
///     type ItemMut = &'a mut T;
///
///     type Iter = std::slice::Iter<'a, T>;
///     type IterMut = std::slice::IterMut<'a, T>;
///
///     fn iter(&'a self) -> Self::Iter {
///         self.data.iter()
///     }
///
///     fn iter_mut(&'a mut self) -> Self::IterMut {
///         self.data.iter_mut()
///     }
/// }
///
/// impl<'a, T: 'a> Collection<'a, T> for MyCollection<T> {
///     fn new_default() -> Self where Self: Sized {
///         MyCollection {
///            data: Vec::new(),
///         }
///     }
///
///     fn add(&mut self, value: T) {
///         self.data.push(value);
///     }
///
///     fn remove(&mut self) -> Option<T> {
///         self.data.pop()
///     }
///
///     fn len(&self) -> usize {
///         self.data.len()
///     }
/// }
/// ```
///
///
/// # Derivable Traits
///
/// The [`Collection`] trait allows the easy implementation of several traits that can be derived
/// through the `derive` macro. These traits can be generically implemented by using the methods
/// in the [`Collection`] trait. Currently, the following traits are derivable:
///
/// - [`FromIterator`]: Creates a new [`Collection`] from an iterator.
/// - [`IntoIterator`]: Creates an iterator from a [`Collection`].
/// - [`Default`]: Creates a new [`Collection`] with a default capacity. Uses the [`new_default`]
/// method.
/// - [`Extend`]: Extends a [`Collection`] with items from an iterator. Uses the [`add`] method.
/// - [`Display`]: Converts a [`Collection`] to a string. Uses the [`iter`] method.
/// - [`NewMacro`]: Adds a macro for easy creation of a new [`Collection`] with the same syntax as
/// the array creation syntax.
/// - [`Drop`]: Drops the [`Collection`] while avoiding memory leaks.
/// - [`Index`]: Allows indexing into a [`Collection`]. However, this this trait could be
/// incompatible with the [`get`] and [`get_mut`] methods.
///
/// Special mention to the [`All`] derive macro, which can be used to derive all traits at once.
///
/// For more information about the derivable traits, see the [`Collection Macros`] module.
///
/// # Safety
///
/// The implementation of the [`Collection`] trait could be unsafe as some of the methods in the
/// trait need the use of unsafe code. However, the different implementations of the [`Collection`]
/// should ensure that the behavior is safe.
///
/// [`new_default`]: Collection::new_default
/// [`with_capacity`]: Collection::with_capacity
/// [`with_approximate_capacity`]: Collection::with_approximate_capacity
/// [`add`]: Collection::add
/// [`remove`]: Collection::remove
/// [`clear`]: Collection::clear
/// [`peek`]: Collection::peek
/// [`peek_mut`]: Collection::peek_mut
/// [`get`]: Collection::get
/// [`get_mut`]: Collection::get_mut
/// [`find`]: Collection::find
/// [`contains`]: Collection::contains
/// [`len`]: Collection::len
/// [`is_empty`]: Collection::is_empty
/// [`ItemRef`]: Iterators::ItemRef
/// [`ItemMut`]: Iterators::ItemMut
/// [`iter`]: Iterators::iter
///
/// [`Collection Macros`]: crate::macros
/// [`FromIterator`]: trait_based_collection_macros::FromIterator
/// [`IntoIterator`]: trait_based_collection_macros::IntoIterator
/// [`Default`]: trait_based_collection_macros::Default
/// [`Extend`]: trait_based_collection_macros::Extend
/// [`Display`]: trait_based_collection_macros::Display
/// [`NewMacro`]: trait_based_collection_macros::NewMacro
/// [`Drop`]: trait_based_collection_macros::Drop
/// [`Index`]: trait_based_collection_macros::Index
/// [`All`]: trait_based_collection_macros::All
pub trait Collection<'a, T>: Iterators<'a, T> {
    /// Creates a new [`Collection`] with a default capacity.
    ///
    /// Generally, this means that the collection will be expandable. This method is useful if you
    /// don't know the amount of items that will be added to the collection . The default capacity
    /// will depend on the implementation of the collection .
    ///
    /// # Examples
    ///
    /// Example using the [`Queue`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, Queue};
    ///
    /// let mut queue: Queue<i32> = Queue::new_default();
    /// ```
    ///
    /// [`Queue`]: crate::queue::Queue
    #[must_use]
    fn new_default() -> Self
    where
        Self: Sized;

    /// Creates a new [`Collection`] with a specific capacity.
    ///
    /// This method is useful if you want to avoid the expense of resizing the collection when
    /// adding items. The capacity will be the specified capacity.
    ///
    /// This method is especially useful for collections of [`FixedSizeCollection`] types. As
    /// linked based data structures don't have an extra cost for adding items, they can be used
    /// with an unlimited capacity.
    ///
    /// # Panics
    ///
    /// This method will panic if the specified capacity is equal to zero.
    ///
    /// # Examples
    ///
    /// Example using the [`Deque`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, Deque};
    ///
    /// let mut deque: Deque<usize> = Deque::with_capacity(10);
    /// ```
    ///
    /// [`Deque`]: crate::queue::Deque
    #[must_use]
    fn with_capacity(capacity: usize) -> Self
    where
        Self: Sized,
    {
        assert!(capacity > 0, "capacity must be greater than zero");
        Self::new_default()
    }

    /// Creates a new [`Collection`] with a capacity that is at least the specified capacity.
    ///
    /// This method is useful if you want to avoid the expense of resizing the collection when
    /// adding items. The capacity will be the specified capacity, with the capacity to be increased
    /// if needed.
    ///
    /// This method is especially useful for collections of [`FixedSizeCollection`] types. As
    /// linked based data structures don't have an extra cost for adding items, they can be used
    /// with an unlimited capacity.
    ///
    /// # Panics
    ///
    /// This method will panic if the specified capacity is equal to zero.
    ///
    /// # Examples
    ///
    /// Example using the [`CircularDeque`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, CircularDeque};
    ///
    /// let mut circular_deque: CircularDeque<usize> = CircularDeque::with_approximate_capacity(10);
    /// ```
    ///
    /// [`CircularDeque`]: crate::queue::CircularDeque
    #[must_use]
    fn with_approximate_capacity(approx_capacity: usize) -> Self
    where
        Self: Sized,
    {
        assert!(
            approx_capacity > 0,
            "approx_capacity must be greater than zero"
        );
        Self::with_capacity(approx_capacity)
    }

    /// Adds an item to the [`Collection`].
    ///
    /// # Examples
    ///
    /// Example using the [`Stack`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, Stack};
    ///
    /// let mut stack = Stack::new_default();
    /// stack.add(10);
    /// assert_eq!(stack.len(), 1);
    /// ```
    ///
    /// [`Stack`]: crate::stack::Stack
    fn add(&mut self, value: T);

    /// Removes an item from the [`Collection`].
    ///
    /// The item that will be removed will depend on the type of data structure. For example,
    /// the [`Stack`] type will remove the last item added to the stack. The [`Queue`] type will
    /// remove the first item added to the queue.
    ///
    /// # Examples
    ///
    /// Example using the [`ArrayStack`]:
    ///
    /// ```
    /// use trait_based_collection::{import, ArrayStack};
    /// import!();
    ///
    /// # fn main() {
    /// let mut stack = array_stack![0, 1, 2, 3, 4];
    ///
    /// for i in (0..5).rev() {
    ///     assert_eq!(stack.remove().unwrap(), i);
    /// }
    ///
    /// assert_eq!(stack.remove(), None);
    /// # }
    /// ```
    ///
    /// [`Stack`]: crate::stack::Stack
    /// [`Queue`]: crate::queue::Queue
    /// [`ArrayStack`]: crate::stack::ArrayStack
    fn remove(&mut self) -> Option<T>;

    /// Clears all items from the [`Collection`] while keeping the capacity.
    ///
    /// This method is useful if you want to reuse the collection . It will not free any memory.
    ///
    /// # Examples
    ///
    /// Example using the [`Queue`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, Queue};
    ///
    /// let mut queue = Queue::new_default();
    /// queue.add(0);
    ///
    /// assert!(!queue.is_empty());
    /// queue.clear();
    /// assert!(queue.is_empty());
    /// ```
    ///
    /// [`Queue`]: crate::queue::Queue
    fn clear(&mut self) {
        while !self.is_empty() {
            self.remove()
                .expect("The collection is not empty, so remove should never return None");
        }
    }

    /// Returns an immutable reference of the item that will be removed next.
    ///
    /// # Examples
    ///
    /// Example using the [`Deque`]:
    ///
    /// ```
    /// use trait_based_collection::{import, Deque};
    /// import!();
    ///
    /// # fn main() {
    /// let mut queue = deque![0, 1, 2, 3, 4];
    ///
    /// assert_eq!(queue.peek(), Some(&0));
    /// # }
    /// ```
    ///
    /// [`Deque`]: crate::queue::Deque
    fn peek(&'a self) -> Option<Self::ItemRef> {
        self.iter().next()
    }

    /// Returns a mutable reference of the item that will be removed next.
    ///
    /// # Examples
    ///
    /// Example using the [`CircularDeque`]:
    ///
    /// ```
    /// use trait_based_collection::{import, CircularDeque};
    /// import!();
    ///
    /// # fn main() {
    /// let mut queue = circular_deque![0, 1, 2, 3, 4];
    ///
    /// assert_eq!(queue.peek(), Some(&0));
    /// # }
    /// ```
    ///
    /// [`CircularDeque`]: crate::queue::CircularDeque
    fn peek_mut(&'a mut self) -> Option<Self::ItemMut> {
        self.iter_mut().next()
    }

    /// Returns a immutable reference to the n-th item in the [`Collection`].
    ///
    /// This should return the same item as if we removed `n-1` items from the [`Collection`] and
    /// returned the last item.
    ///
    /// # Examples
    ///
    /// Example using the [`Stack`]:
    ///
    /// ```
    /// use trait_based_collection::{import, Stack};
    /// import!();
    ///
    /// # fn main() {
    /// let mut stack = stack![0, 1, 2, 3, 4];
    ///
    /// assert_eq!(stack.get(3), Some(&1));
    /// # }
    /// ```
    ///
    /// [`Stack`]: crate::stack::Stack
    fn get(&'a self, index: usize) -> Option<Self::ItemRef> {
        self.iter().nth(index)
    }

    /// Returns a mutable reference to the n-th item in the [`Collection`].
    ///
    /// This should return the same item as if we removed `n-1` items from the [`Collection`] and
    /// returned the last item.
    ///
    /// # Examples
    ///
    /// Example using the [`ArrayStack`]:
    ///
    /// ```
    /// use trait_based_collection::{import, ArrayStack};
    /// import!();
    ///
    /// # fn main() {
    /// let mut stack = array_stack![0, 1, 2, 3, 4];
    ///
    /// assert_eq!(stack.get_mut(1), Some(&mut 3));
    /// # }
    /// ```
    ///
    /// [`ArrayStack`]: crate::stack::ArrayStack
    fn get_mut(&'a mut self, index: usize) -> Option<Self::ItemMut> {
        self.iter_mut().nth(index)
    }

    /// Searches for an item in the [`Collection`] and returns its index if found.
    /// Returns `None` if the item is not found.
    ///
    /// The default implementation uses [`iter`] to find the item with a linear search.
    ///
    /// # Examples
    ///
    /// Example using the [`Queue`]:
    ///
    /// ```
    /// use trait_based_collection::{import, Queue};
    /// import!();
    ///
    /// # fn main() {
    /// let mut queue = queue![4, 1, 0, 2, 3];
    ///
    /// assert_eq!(queue.find(&2), Some(3));
    /// # }
    /// ```
    ///
    /// [`Queue`]: crate::queue::Queue
    /// [`iter`]: Iterators::iter
    fn find(&'a self, value: &T) -> Option<usize>
    where
        T: PartialEq,
    {
        self.iter().position(|x| *x == *value)
    }

    /// Checks if an item is in the [`Collection`].
    ///
    /// The default implementation uses [`find`] to check if the item is in the collection .
    ///
    /// # Examples
    ///
    /// Example using the [`Deque`]:
    ///
    /// ```
    /// use trait_based_collection::{import, Deque};
    /// import!();
    ///
    /// # fn main() {
    /// let mut queue = deque![0, 1, 2, 3, 4];
    ///
    /// assert!(queue.contains(&3));
    /// # }
    /// ```
    ///
    /// [`Deque`]: crate::queue::Deque
    /// [`find`]: Collection::find
    fn contains(&'a self, value: &T) -> bool
    where
        T: PartialEq,
    {
        self.find(value).is_some()
    }

    /// Returns the number of items in the [`Collection`].
    ///
    /// # Examples
    ///
    /// Example using the [`CircularDeque`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, CircularDeque};
    ///
    /// let mut queue = CircularDeque::new_default();
    /// assert_eq!(queue.len(), 0);
    ///
    /// for i in 0..10 {
    ///    queue.add(i);
    /// }
    ///
    /// assert_eq!(queue.len(), 10);
    /// ```
    ///
    /// [`CircularDeque`]: crate::queue::CircularDeque
    fn len(&self) -> usize;

    /// Checks if the [`Collection`] is empty.
    ///
    /// # Examples
    ///
    /// Example using the [`Stack`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, Stack};
    ///
    /// let mut stack = Stack::new_default();
    ///
    /// assert!(stack.is_empty());
    /// stack.add(0);
    /// assert!(!stack.is_empty());
    /// ```
    ///
    /// [`Stack`]: crate::stack::Stack
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Different modes of action when the [`FixedSizeCollection`] is full. Depending on the mode, the
/// collection will behave differently through the [`check_expansion`] method.
///
/// There are four modes of expansion:
/// 1. [`Panic`] - The collection will panic when the capacity is reached.
/// 2. [`Ignore`] - The collection will ignore the addition of the new item.
/// 3. [`Overwrite`] - The collection will overwrite the an item when the capacity is reached.
/// 4. [`Expand`] - The collection will expand the capacity by a specific factor. The factor must
///     be greater than `1.0`. If the factor is `1.0`, the function will `panic!`. This is the
///     default mode with a factor of `2.0`.
///
/// # Examples
///
/// Example on how the expansion is checked in [`FixedSizeCollection`] through the
/// [`check_expansion`] method:
///
/// ```
/// use trait_based_collection::prelude::*;
///
/// fn check_expansion<'a, T, C: FixedSizeCollection<'a, T>>(mut collection: C) -> bool {
///     if collection.is_full() {
///         match collection.mode() {
///             ExpansionMode::Panic => {
///                 panic!("The collection is full");
///             }
///             ExpansionMode::Ignore => {
///                 return true;
///             }
///             ExpansionMode::Overwrite => {
///                 collection.remove();
///             }
///             ExpansionMode::Expand(factor) => {
///                 if *factor < 1.0 {
///                     panic!("Expand factor must be greater than 1");
///                 }
///                 let size = ((*factor - 1.0) * collection.capacity() as f64).floor() as usize;
///                 collection.expand(size);
///             }
///         }
///     }
///     false
/// }
/// ```
///
/// [`Panic`]: ExpansionMode::Panic
/// [`Ignore`]: ExpansionMode::Ignore
/// [`Overwrite`]: ExpansionMode::Overwrite
/// [`Expand`]: ExpansionMode::Expand
#[derive(Debug)]
pub enum ExpansionMode {
    /// The collection will panic when the capacity is reached.
    Panic,
    /// The collection will ignore the addition of the new item.
    Ignore,
    /// The collection will overwrite the an item when the capacity is reached. This means that
    /// before the new item is added, an item is removed by calling the [`remove`] method.
    ///
    /// [`remove`]: Collection::remove
    Overwrite,
    /// The collection will expand the capacity by a specific factor. The factor must be greater
    /// than `1.0`. If the factor is `1.0`, the function will `panic!`. This is the default mode
    /// with a factor of `2.0`.
    Expand(f64),
}

impl PartialEq for ExpansionMode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Panic, Self::Panic)
            | (Self::Ignore, Self::Ignore)
            | (Self::Overwrite, Self::Overwrite) => true,
            (ExpansionMode::Expand(a), ExpansionMode::Expand(b)) => a == b,
            _ => false,
        }
    }
}

impl Default for ExpansionMode {
    fn default() -> Self {
        Self::Expand(2.0)
    }
}

/// A [`Collection`] that can easily be expanded, as the capacity is fixed. Normally, this are data
/// structures that use a fixed size buffer in memory ([`Array`]-like).
///
/// Similar to [`Collection`], the [`FixedSizeCollection`] is a trait that is generic over any type
/// without the need of any extra traits. This allows the user to create a collection of any type
/// that they want.
///
/// To create a new [`FixedSizeCollection`], the user must add the following extra code into the
/// [`add`] method at the beginning of the method. This code will manage the expansion of the
/// collection depending on the [`ExpansionMode`] of the collection :
///
/// ```text
/// if check_expansion(self) {
///     return;
/// }
/// ```
///
/// An alternative way is to call the [`check_expansion_add`] macro. This macro will add the
/// the previous code into the [`add`] method.
///
/// For a full example, see the Examples section.
///
/// The trait provide extra methods related with the capacity of the collection . The capacity is
/// the amount of items that the collection can hold. The [`FixedSizeCollection`] provides the
/// following methods:
///
/// - [`with_mode`] - Creates a new [`FixedSizeCollection`] with the specified capacity and
/// [`ExpansionMode`].
/// - [`capacity`] - Returns the maximum amount of items that the collection can hold.
/// - [`expand`] - Expands the capacity of the collection by a specific amount. This amount or more
/// will be added to the capacity.
/// - [`is_full`] - Returns `true` if the collection is full. Checks if the length of the collection
/// is equal to the capacity.
/// - [`mode`] - Returns the [`ExpansionMode`] of expansion of the collection .
///
/// For implementation of the [`FixedSizeCollection`] data structure, there also exists the
/// following method:
///
/// - [`check_expansion`] - Checks if the collection is full and if it is, it will behave depending
/// on the [`mode`] of the collection .
///
/// # Examples
///
/// Expands the example shown in [`Collection`] by modifying a bit the struct with a mode and
/// implementing the [`FixedSizeCollection`] trait. The example contains only the modified code.
///
/// ```
/// use trait_based_collection::{prelude::*, macros::{check_expansion_add, All}};
///
/// #[derive(All)]
/// struct MyCollection<T> {
///     data: Vec<T>,
///     mode: ExpansionMode,
/// }
/// #
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
///
/// impl<'a, T: 'a> Collection<'a, T> for MyCollection<T> {
///     fn new_default() -> Self where Self: Sized {
///         MyCollection::with_mode(16, ExpansionMode::default())
///     }
///
///     fn with_capacity(capacity: usize) -> Self {
///         MyCollection::with_mode(capacity, ExpansionMode::Panic)
///     }
///
///     fn with_approximate_capacity(approx_capacity: usize) -> Self{
///         MyCollection::with_mode(approx_capacity, ExpansionMode::default())
///     }
///
///     #[check_expansion_add]
///     fn add(&mut self, value: T) {
///         self.data.push(value);
///     }
/// #
/// #     fn remove(&mut self) -> Option<T> {
/// #         self.data.pop()
/// #     }
/// #
/// #     fn len(&self) -> usize {
/// #         self.data.len()
/// #     }
/// }
///
/// impl<'a, T: 'a> FixedSizeCollection<'a, T> for MyCollection<T> {
///     fn with_mode(capacity: usize, mode: ExpansionMode) -> Self {
///         assert_ne!(capacity, 0, "Capacity must be greater than 0");
///         MyCollection {
///            data: Vec::with_capacity(capacity),
///            mode,
///         }
///     }
///
///     fn capacity(&self) -> usize {
///         self.data.capacity()
///     }
///
///     fn expand(&mut self, extra_size: usize) {
///         self.data.reserve(extra_size);
///     }
///
///     fn mode(&self) -> &ExpansionMode {
///         &self.mode
///     }
/// }
/// ```
///
/// # Safety
///
/// The [`FixedSizeCollection`] trait is currently safe as it is based on the [`Vec`]
/// implementation. However, in the future, [`Vec`] could also be implemented in the project and
/// the [`FixedSizeCollection`] trait would be unsafe. Similarly to [`Collection`], the trait
/// is implemented in unsafe code but the usage of the trait should be safe.
///
/// [`Array`]: https://doc.rust-lang.org/std/primitive.array.html
/// [`add`]: Collection::add
/// [`check_expansion_add`]: macro@trait_based_collection_macros::check_expansion_add
/// [`capacity`]: FixedSizeCollection::capacity
/// [`expand`]: FixedSizeCollection::expand
/// [`is_full`]: FixedSizeCollection::is_full
/// [`mode`]: FixedSizeCollection::mode
/// [`with_mode`]: FixedSizeCollection::with_mode
#[allow(clippy::module_name_repetitions)]
pub trait FixedSizeCollection<'a, T>: Collection<'a, T> {
    /// Creates a new fixed size [`Collection`] with the specified capacity and [`ExpansionMode`].
    ///
    /// # Panics
    ///
    /// This method will panic if the specified capacity is equal to zero.
    ///
    /// # Examples
    ///
    /// Example using [`ArrayStack`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, ArrayStack};
    ///
    /// let mut stack: ArrayStack<i32> = ArrayStack::with_mode(16, ExpansionMode::Expand(2.0));
    /// assert_eq!(stack.capacity(), 16);
    /// assert_eq!(stack.mode(), &ExpansionMode::Expand(2.0));
    /// ```
    ///
    /// [`ArrayStack`]: crate::stack::ArrayStack
    #[must_use]
    fn with_mode(capacity: usize, mode: ExpansionMode) -> Self
    where
        Self: Sized;

    /// Returns the maximum amount of items that the collection can hold without expanding.
    ///
    /// The number of items on the [`FixedSizeCollection`] can never be greater than the capacity.
    ///
    /// # Examples
    ///
    /// Example using [`CircularDeque`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, CircularDeque};
    ///
    /// let mut queue: CircularDeque<usize> = CircularDeque::with_capacity(10);
    /// assert_eq!(queue.capacity(), 10);
    /// ```
    ///
    /// [`CircularDeque`]: crate::queue::CircularDeque
    fn capacity(&self) -> usize;

    /// Expands the capacity of the collection by at least the specified amount. This amount or more
    /// will be dded to the capacity.
    ///
    /// This method is called automatically if the [`mode`] of the collection is [`Expand`], it will
    /// be called when the collection is full through the [`check_expansion`] method.
    ///
    /// This method ensures that after the expansion, the integrity of the [`FixedSizeCollection`]
    /// is not compromised.
    ///
    /// # Examples
    ///
    /// Example using [`ArrayStack`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, ArrayStack};
    ///
    /// let mut stack: ArrayStack<usize> = ArrayStack::with_capacity(10);
    /// assert_eq!(stack.capacity(), 10);
    /// stack.expand(10);
    /// assert!(stack.capacity() >= 20);
    /// ```
    ///
    /// [`mode`]: FixedSizeCollection::mode
    /// [`Expand`]: ExpansionMode::Expand
    /// [`ArrayStack`]: crate::stack::ArrayStack
    fn expand(&mut self, extra_size: usize);

    /// Checks if the number of items in the [`FixedSizeCollection`] is equal to the capacity.
    ///
    /// # Examples
    ///
    /// Example using [`CircularDeque`]:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, CircularDeque};
    ///
    /// let mut queue = CircularDeque::with_capacity(10);
    /// assert!(!queue.is_full());
    ///
    /// for i in 0..10 {
    ///    queue.add(i);
    /// }
    /// assert!(queue.is_full());
    /// ```
    ///
    /// [`CircularDeque`]: crate::queue::CircularDeque
    fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Returns the [`ExpansionMode`] of the collection . This is used to determine how the
    /// collection will behave when it is full.
    ///
    /// The possibility of modifying the [`ExpansionMode`] will be determined by the implementation.
    /// The built-in implementations of [`FixedSizeCollection`] will allow modifications through
    /// a public attribute.
    ///
    /// # Examples
    ///
    /// Example using [`ArrayStack`] with default constructor:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, ArrayStack};
    ///
    /// let mut stack: ArrayStack<u8> = ArrayStack::default();
    /// assert_eq!(stack.mode(), &ExpansionMode::default());
    /// ```
    ///
    /// Another example but using the [`with_capacity`] constructor:
    ///
    /// ```
    /// use trait_based_collection::{prelude::*, ArrayStack};
    ///
    /// let mut stack: ArrayStack<u8> = ArrayStack::with_capacity(10);
    /// assert_eq!(stack.mode(), &ExpansionMode::Panic);
    /// ```
    ///
    /// [`ArrayStack`]: crate::stack::ArrayStack
    /// [`with_capacity`]: crate::stack::ArrayStack::with_capacity
    fn mode(&self) -> &ExpansionMode;
}

/// Checks if the collection is full and if it is, expands the collection depending on the
/// [`ExpansionMode`]. Also, returns `true` if the [`add`] method should finish execution.
///
/// This method should be called before adding an item to the collection . If the collection is
/// full, the method will do:
/// - [`Panic`]: The method will panic.
/// - [`Ignore`]: The item will not be added to the collection and will npt
/// - [`Overwrite`]: An item will be removed from the collection and the new item will be added.
/// In this case, the [`remove`] method will be called.
/// - [`Expand`]: The collection will be expanded and the item will be added. In this case, the
/// [`expand`] method will be called.
///
/// Instead of using this method inside the [`add`] method, it is recommended to use the
/// [`check_expansion_add`] macro.
///
/// # Panics
///
/// This method will panic if [`mode`] is [`Panic`] and the collection is full.
///
/// # Examples
///
/// Example without using [`check_expansion_add`] macro on an [`add`] method:
///
/// ```
/// # use trait_based_collection::{prelude::*, macros::All};
/// use trait_based_collection::macros::check_expansion_add;
/// #
/// # #[derive(All)]
/// # struct MyCollection<T> {
/// #     data: Vec<T>,
/// #     mode: ExpansionMode,
/// # }
/// #
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
/// #         MyCollection::with_mode(16, ExpansionMode::default())
/// #     }
/// #
/// #     fn with_capacity(capacity: usize) -> Self {
/// #         MyCollection::with_mode(capacity, ExpansionMode::Panic)
/// #     }
/// #
/// #     fn with_approximate_capacity(approx_capacity: usize) -> Self{
/// #         MyCollection::with_mode(approx_capacity, ExpansionMode::default())
/// #     }
/// #
///     #[check_expansion_add]
///     fn add(&mut self, value: T) {
///         self.data.push(value);
///     }
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
/// # impl<'a, T: 'a> FixedSizeCollection<'a, T> for MyCollection<T> {
/// #     fn with_mode(capacity: usize, mode: ExpansionMode) -> Self {
/// #         assert_ne!(capacity, 0, "Capacity must be greater than 0");
/// #         MyCollection {
/// #            data: Vec::with_capacity(capacity),
/// #            mode,
/// #         }
/// #     }
/// #
/// #     fn capacity(&self) -> usize {
/// #         self.data.capacity()
/// #     }
/// #
/// #     fn expand(&mut self, extra_size: usize) {
/// #         self.data.reserve(extra_size);
/// #     }
/// #
/// #     fn mode(&self) -> &ExpansionMode {
/// #         &self.mode
/// #     }
/// # }
/// ```
///
/// Alternative example without using [`check_expansion_add`] macro on an [`add`] method:
///
/// ```
/// # use trait_based_collection::{prelude::*, macros::All};
/// use trait_based_collection::collection::check_expansion;
/// #
/// # #[derive(All)]
/// # struct MyCollection<T> {
/// #     data: Vec<T>,
/// #     mode: ExpansionMode,
/// # }
/// #
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
/// #         MyCollection::with_mode(16, ExpansionMode::default())
/// #     }
/// #
/// #     fn with_capacity(capacity: usize) -> Self {
/// #         MyCollection::with_mode(capacity, ExpansionMode::Panic)
/// #     }
/// #
/// #     fn with_approximate_capacity(approx_capacity: usize) -> Self{
/// #         MyCollection::with_mode(approx_capacity, ExpansionMode::default())
/// #     }
/// #
///     fn add(&mut self, value: T) {
///         if check_expansion(self) {
///             return;
///         }
///         self.data.push(value);
///     }
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
/// # impl<'a, T: 'a> FixedSizeCollection<'a, T> for MyCollection<T> {
/// #     fn with_mode(capacity: usize, mode: ExpansionMode) -> Self {
/// #         assert_ne!(capacity, 0, "Capacity must be greater than 0");
/// #         MyCollection {
/// #            data: Vec::with_capacity(capacity),
/// #            mode,
/// #         }
/// #     }
/// #
/// #     fn capacity(&self) -> usize {
/// #         self.data.capacity()
/// #     }
/// #
/// #     fn expand(&mut self, extra_size: usize) {
/// #         self.data.reserve(extra_size);
/// #     }
/// #
/// #     fn mode(&self) -> &ExpansionMode {
/// #         &self.mode
/// #     }
/// # }
/// ```
///
/// [`add`]: Collection::add
/// [`Panic`]: ExpansionMode::Panic
/// [`Ignore`]: ExpansionMode::Ignore
/// [`Overwrite`]: ExpansionMode::Overwrite
/// [`remove`]: Collection::remove
/// [`Expand`]: ExpansionMode::Expand
/// [`expand`]: FixedSizeCollection::expand
/// [`mode`]: FixedSizeCollection::mode
pub fn check_expansion<'a, T, C: FixedSizeCollection<'a, T>>(collection: &mut C) -> bool {
    if collection.is_full() {
        match collection.mode() {
            ExpansionMode::Panic => {
                panic!("The collection is full");
            }
            ExpansionMode::Ignore => {
                return true;
            }
            ExpansionMode::Overwrite => {
                collection.remove(); // Tries to remove an element from the collection
            }
            ExpansionMode::Expand(factor) => {
                assert!(*factor >= 1.0, "Expand factor must be greater than 1");
                // We are sure that the cast is safe
                #[allow(clippy::cast_precision_loss)]
                #[allow(clippy::cast_sign_loss)]
                #[allow(clippy::cast_possible_truncation)]
                let size = ((*factor - 1.0) * collection.capacity() as f64).floor() as usize;
                collection.expand(size);
            }
        }
    }
    false
}

#[cfg(test)]
mod test_fixed_size_collection {
    use super::*;
    use crate::{ArrayStack, CircularDeque};
    use trait_based_collection_macros::test_collection;

    #[test_collection(ArrayStack, CircularDeque)]
    fn test_capacity<C: FixedSizeCollection<i32>>(_collection: C) {
        let mut collection = C::with_capacity(10);
        assert_eq!(collection.capacity(), 10);

        for i in 0..10 {
            collection.add(i);
        }
        assert_eq!(collection.capacity(), 10);

        let mut collection: C<i32> = C::with_capacity(100);
        assert_eq!(collection.capacity(), 100);

        for i in 0..100 {
            collection.add(i);
        }
        assert_eq!(collection.capacity(), 100);

        let collection: C<i32> = C::new_default();
        assert_eq!(collection.capacity(), 16);
    }

    #[test_collection(ArrayStack, CircularDeque)]
    fn test_expand<C: FixedSizeCollection<i32>>(_collection: C) {
        let mut collection = C::with_capacity(13);
        assert_eq!(collection.capacity(), 13);
        // Expand with empty collection
        collection.expand(11);
        assert!(collection.capacity() >= 24);

        // Simulates random usage of collection
        for _ in 0..7 {
            for i in 0..5 {
                collection.add(i);
            }
            for _ in 0..5 {
                collection.remove().unwrap();
            }
        }
        // Fill half-collection
        for i in 0..12 {
            collection.add(i);
        }
        assert_eq!(collection.len(), 12);
        assert!(collection.capacity() >= 24);

        // Expand with half-collection
        collection.expand(3);
        assert!(collection.capacity() >= 27);
    }

    #[test_collection(ArrayStack, CircularDeque)]
    fn test_is_full<C: FixedSizeCollection<i32>>(_collection: C) {
        let mut collection = C::with_mode(10, ExpansionMode::Expand(2.0));
        assert!(!collection.is_full());
        for i in 0..10 {
            collection.add(i);
        }
        assert!(collection.is_full());

        // Expands the collection
        collection.add(10);
        assert!(!collection.is_full());
    }

    #[test_collection(ArrayStack, CircularDeque)]
    fn test_mode<C: FixedSizeCollection<i32>>(_collection: C) {
        let collection: C<i32> = C::with_mode(10, ExpansionMode::Expand(2.0));
        assert_eq!(collection.mode(), &ExpansionMode::Expand(2.0));

        let collection: C<i32> = C::with_mode(10, ExpansionMode::Overwrite);
        assert_eq!(collection.mode(), &ExpansionMode::Overwrite);

        let collection: C<i32> = C::with_mode(10, ExpansionMode::Ignore);
        assert_eq!(collection.mode(), &ExpansionMode::Ignore);

        let collection: C<i32> = C::with_mode(10, ExpansionMode::Panic);
        assert_eq!(collection.mode(), &ExpansionMode::Panic);
    }
}

#[cfg(test)]
mod test_modes {
    use super::*;
    use crate::{ArrayStack, CircularDeque};
    use trait_based_collection_macros::test_collection;

    #[test_collection(ArrayStack, CircularDeque; should_panic)]
    fn test_mode_panic<C: FixedSizeCollection<i32>>(_collection: C) {
        let mut collection = C::with_mode(5, ExpansionMode::Panic);
        for i in 0..5 {
            collection.add(i);
        }

        // Chis should panic
        collection.add(5);
    }

    #[test_collection(ArrayStack, CircularDeque)]
    fn test_mode_ignore<C: FixedSizeCollection<i32> + IntoIterator<Item = i32>>(_collection: C) {
        let mut collection = C::with_mode(5, ExpansionMode::Ignore);
        for i in 0..5 {
            collection.add(i);
        }

        for i in 10..15 {
            collection.add(i);
            assert_eq!(collection.len(), 5);
            assert_eq!(collection.capacity(), 5);
        }
        // Only numbers of the first loop should be in the collection
        let mut collection_vec = collection.into_iter().collect::<Vec<_>>();
        collection_vec.sort_unstable();
        assert_eq!(collection_vec, vec![0, 1, 2, 3, 4]);
    }

    #[test_collection(ArrayStack, CircularDeque)]
    fn test_mode_overwrite<C: FixedSizeCollection<i32> + IntoIterator<Item = i32>>(_collection: C) {
        let mut collection = C::with_mode(5, ExpansionMode::Overwrite);
        for i in 0..5 {
            collection.add(i);
        }

        for i in 10..15 {
            collection.add(i);
            assert_eq!(collection.len(), 5);
            assert_eq!(collection.capacity(), 5);
        }

        // At least one of the numbers of the should be changed in the second loop
        let mut collection_vec = collection.into_iter().collect::<Vec<_>>();
        collection_vec.sort_unstable();
        assert_ne!(collection_vec, vec![0, 1, 2, 3, 4]);
    }

    #[test_collection(ArrayStack, CircularDeque)]
    fn test_mode_expand<C: FixedSizeCollection<i32> + IntoIterator<Item = i32>>(_collection: C) {
        let mut collection = C::with_mode(5, ExpansionMode::Expand(2.0));
        for i in 0..5 {
            collection.add(i);
        }

        for i in 10..15 {
            collection.add(i);
            assert_ne!(collection.len(), 5);
            assert_ne!(collection.capacity(), 5);
        }
        assert!(collection.capacity() >= 10);

        // All numbers should be in the collection
        let mut collection_vec = collection.into_iter().collect::<Vec<_>>();
        collection_vec.sort_unstable();
        assert_eq!(collection_vec, vec![0, 1, 2, 3, 4, 10, 11, 12, 13, 14]);
    }
}
