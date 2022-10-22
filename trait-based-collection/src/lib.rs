//! A collection of data structures that implement the [`Collection`] trait, allowing for a common
//! interface for all the data structures in this crate. This crate is intended to be a proof of
//! concept a common interface for all the data structures in Rust. Not all the data structures
//! are implemented in this crate, but the ones that are implemented are:
//!
//! - [`Queue`]: A `FIFO` data structure based on linked nodes.
//! - [`Deque`]: A `FIFO` and `LIFO` data structure based on linked nodes.
//! - [`CircularDeque`]: A `FIFO` and `LIFO` data structure based on a circular array.
//! - [`Stack`]: A `LIFO` data structure based on a linked nodes.
//! - [`ArrayStack`]: A `LIFO` data structure based on a fixed size array.
//! - [`BinaryHeap`]: A `PriorityQueue` data structure based on a binary heap.
//!
//! The crate also contains the following traits:
//!
//! - [`Collection`]: A trait that defines the common interface for all the data structures in this
//! crate.
//! - [`FixedSizeCollection`]: A trait that defines the common interface for all the data structures
//! in this crate that have a fixed size.
//! - [`Iterators`]: A trait that defines the common interface for all the iterators in this crate.
//! - [`DequeCollection`]: A trait that defines the common interface for all the data structures in
//! this crate that are both `FIFO` and `LIFO`.
//!
//! The crate also contains the following macros for easily creating data structures:
//! - [`queue!`]: A macro that creates a [`Queue`] data structure.
//! - [`deque!`]: A macro that creates a [`Deque`] data structure.
//! - [`circular_deque!`]: A macro that creates a [`CircularDeque`] data structure.
//! - [`stack!`]: A macro that creates a [`Stack`] data structure.
//! - [`array_stack!`]: A macro that creates a [`ArrayStack`] data structure.
//! - [`binary_heap!`]: A macro that creates a [`BinaryHeap`] data structure.
//!
//! The crate also contain extra modules for creating new data structures and for creating macros
//! that can be used to add functionality to the data structures in this crate. For more information
//! about these modules, see the documentation of [`macros`].
//!
//! # Example
//!
//! ```
//! use trait_based_collection::{import, Deque};
//! import!();
//!
//! # fn main() {
//! let mut deque = deque![1, 2, 3];
//!
//! for i in 4..=10 {
//!    deque.add(i);
//! }
//!
//! for i in 1..=10 {
//!    assert_eq!(deque.remove(), Some(i));
//! }
//! # }
//! ```
#![warn(missing_docs)]
#![allow(clippy::module_name_repetitions)]
extern crate trait_based_collection_macros;

pub mod collection;
pub mod priority_queue;
pub mod queue;
pub mod stack;

pub use self::collection::{Collection, ExpansionMode, FixedSizeCollection, Iterators};
pub use self::priority_queue::BinaryHeap;
pub use self::queue::{CircularDeque, Deque, DequeCollection, Queue};
pub use self::stack::{ArrayStack, Stack};

/// A collection of all the procedural macros used in this crate. This macros can be divided into
/// two categories:
///
/// - **Derive macros**: These macros are used to derive traits for the data structures in this
/// crate. These macros are:
///    - [`Default`]: Default implementation for creating a new instance of the data structure. This
/// macro is used to implement the [`Default`](std::default::Default) trait.
///    - [`Display`]: Allows the data structure to be printed using the
/// [`Display`](std::fmt::Display) trait.
///    - [`Drop`]: Allows the data structure to be safely dropped using the [`Drop`](std::ops::Drop)
/// trait.
///    - [`Extend`]: Allows the data structure to be extended using the
/// [`Extend`](std::iter::Extend) trait.
///    - [`FromIterator`]: Allows the data structure to be created from an iterator using the
/// [`FromIterator`](std::iter::FromIterator) trait.
///    - [`Index`]: Allows the data structure to be indexed using the [`Index`](std::ops::Index)
/// trait.
///   - [`IntoIterator`]: Allows the data structure to be iterated using the
/// [`IntoIterator`](std::iter::IntoIterator) trait.
///   - [`NewMacro`]: Allows the data structure to be created a macro with the same features as the
/// [`vec!`](std::vec!) macro.
///   - [`All`]: Allows the data structure to derive all the above traits.
///
/// - **Attribute macros**: These macros are used to add functionality to the data structures in
/// this crate. These macros are:
///   - [`check_expansion_add`]: This macro is used to add the [`check_expansion`] method to the
/// the beginning of the [`add`] method. This macro can be used for any data structure that
/// implements the [`FixedSizeCollection`] trait.
///
/// [`Default`]: trait_based_collection_macros::Default
/// [`Display`]: trait_based_collection_macros::Display
/// [`Drop`]: trait_based_collection_macros::Drop
/// [`Extend`]: trait_based_collection_macros::Extend
/// [`FromIterator`]: trait_based_collection_macros::FromIterator
/// [`Index`]: trait_based_collection_macros::Index
/// [`IntoIterator`]: trait_based_collection_macros::IntoIterator
/// [`NewMacro`]: trait_based_collection_macros::NewMacro
/// [`All`]: trait_based_collection_macros::All
/// [`check_expansion_add`]: trait_based_collection_macros::check_expansion_add
/// [`check_expansion`]: crate::collection::check_expansion
/// [`add`]: Collection::add
/// [`FixedSizeCollection`]: FixedSizeCollection
pub mod macros {
    pub use trait_based_collection_macros::{
        check_expansion_add, All, Default, Display, Drop, Extend, FromIterator, Index,
        IntoIterator, NewMacro,
    };
}

/// A module that contains all the traits that are used in this crate. This module is meant to be
/// used as a total import using the `prelude::*` syntax. The module also contains a macro that
/// creates the prelude for this crate allowing to also import the macros in this crate.
///
/// This macro avoids the need to write the following code:
/// ```
/// use trait_based_collection::prelude::*;
/// #[macro_use]
/// use trait_based_collection;
/// ```
/// Instead, the following code can be used:
/// ```
/// use trait_based_collection::import;
/// import!();
/// # fn main() {}
/// ```
pub mod prelude {
    pub use super::collection::{Collection, ExpansionMode, FixedSizeCollection, Iterators};
    pub use super::queue::DequeCollection;

    /// Creates the prelude for this crate. This macro is meant to a substitute for the
    /// `use trait_based_collection::prelude::*` statement if the macros in this crate are also needed.
    ///
    /// # Example
    /// ```
    /// use trait_based_collection::import;
    /// import!();
    /// # fn main() {}
    /// ```
    #[macro_export]
    macro_rules! import {
        () => {
            use trait_based_collection::prelude::*;
            // We only need the macros from this crate so we can use a dummy name.
            #[macro_use]
            extern crate trait_based_collection as _;
        };
    }
}
