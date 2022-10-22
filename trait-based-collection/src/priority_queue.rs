//! A collection of different implementations of priority queues. The priority queue is a data
//! structure that allows you to insert elements into it and then retrieve them in order of
//! priority. The priority is determined through a comparator function that is passed to the
//! priority queue.
//!
//! Currently, the following implementations are available:
//!
//! - [`BinaryHeap`]: A binary heap implementation of a priority queue using an array.
//!
//! For more information, see the respective structs' documentation.
#![warn(missing_docs)]
use crate::collection::{Collection, ExpansionMode, FixedSizeCollection, Iterators};
use std::cmp::Ordering;
use std::fmt::Debug;
use std::ops::{Deref, DerefMut};
use trait_based_collection_macros::{
    internal_check_expansion_add, Default, Display, Drop, Extend, FromIterator, IntoIterator,
    NewMacro,
};

/// A mutable reference to an element in a [`BinaryHeap`] that can be used to modify the element
/// while maintaining the heap property. The element is only modified when the `PeekMut` is
/// dropped and the user has tried to modify the element (by mutably dereferencing the `PeekMut`).
/// If the user has not tried to modify the element, the element is not modified.
pub struct PeekMut<'a, T>
where
    T: 'a + Ord,
{
    /// A mutable reference to the heap.
    heap: &'a mut BinaryHeap<T>,
    /// The index of the element in the heap.
    index: usize,
    /// Whether or not the element has been modified.
    modified: bool,
}

impl<'a, T> PeekMut<'a, T>
where
    T: 'a + Ord,
{
    /// Creates a new `PeekMut` with the given heap and index and sets `modified` to `false`.
    ///
    /// # Safety
    ///
    /// The index must be a valid index in the heap.
    pub fn new(heap: &'a mut BinaryHeap<T>, index: usize) -> Self {
        PeekMut {
            heap,
            index,
            modified: false,
        }
    }
}

impl<T> Drop for PeekMut<'_, T>
where
    T: Ord,
{
    fn drop(&mut self) {
        if self.modified {
            self.heap.heapify_both(self.index);
        }
    }
}

impl<T> Deref for PeekMut<'_, T>
where
    T: Ord,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.heap.data[self.index]
    }
}
impl<T> DerefMut for PeekMut<'_, T>
where
    T: Ord,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.modified = true; // The element may be modified.
        &mut self.heap.data[self.index]
    }
}

impl<T> Debug for PeekMut<'_, T>
where
    T: Ord + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_tuple("PeekMut")
            .field(&self.heap.data[self.index])
            .finish()
    }
}

impl<'a, T> PartialEq for PeekMut<'a, T>
where
    T: 'a + Ord,
{
    fn eq(&self, other: &Self) -> bool {
        self.heap.data[self.index] == other.heap.data[other.index]
    }
}

/// An implementation of a priority queue using a binary heap. The binary heap is implemented using
/// an array. The binary heap is a complete binary tree, meaning that every level of the tree is
/// filled except for the last level, which is filled from left to right. The binary heap is stored
/// using a function that determines the order of the elements in the heap.
///
/// The default heap function is equivalent to a min-heap, meaning that the element with the
/// smallest value is at the top of the heap. For a max-heap, the heap can be created using the
/// [`max_heap`] function.
///
/// # Examples
/// ```
/// use trait_based_collection::{prelude::*, BinaryHeap};
///
/// let mut heap = BinaryHeap::min_heap(16, ExpansionMode::Expand(2.0));
/// heap.add(5);
/// heap.add(3);
/// heap.add(7);
/// heap.add(1);
///
/// assert_eq!(heap.remove(), Some(1));
/// assert_eq!(heap.remove(), Some(3));
/// assert_eq!(heap.remove(), Some(5));
/// assert_eq!(heap.remove(), Some(7));
/// assert_eq!(heap.remove(), None);
/// ```
///
/// [`max_heap`]: #method.max_heap
#[derive(Default, Display, Drop, Extend, FromIterator, IntoIterator, NewMacro)]
pub struct BinaryHeap<T>
where
    T: Ord,
{
    /// The data stored in the heap using an array.
    data: Vec<T>,
    /// The function that determines the order of the elements in the heap.
    function: fn(&T, &T) -> Ordering,
    /// The current mode of expansion of the deque that determinate the behaviour the collection is
    /// full. See [`ExpansionMode`] for more information.
    ///
    /// [`ExpansionMode`]: crate::collection::ExpansionMode
    pub mode: ExpansionMode,
}

impl<T> Debug for BinaryHeap<T>
where
    T: Ord + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("Heap")
            .field("data", &self.data)
            .field("mode", &self.mode)
            .finish()
    }
}

/// A mutable iterator over the elements of a [`BinaryHeap`]. The order of the elements is
/// guaranteed to be the same as the order as if the elements were removed from the heap. However,
/// even if an element is modified, the heap property will be maintained from the point of view of
/// when the iterator was created. However, the heap will be modified once the mutable reference to
/// the element is dropped. For more information, see the documentation for [`PeekMut`].
///
/// The elements of the vector are sorted using an array sort, which means that the complexity of
/// the iterator is `O(n log n)`.
pub struct BinaryHeapIterMut<'a, T>
where
    T: 'a + Ord,
{
    /// A vector of mutable references to the elements in the heap.
    data: Vec<PeekMut<'a, T>>,
}

impl<T> BinaryHeapIterMut<'_, T>
where
    T: Ord,
{
    /// Creates a new `BinaryHeapIterMut` with the given a mutable reference to the heap. To ensure
    /// the order of the elements, the elements are sorted using a an array sorting algorithm, which
    /// means that the complexity is `O(n log n)`.
    fn new(heap: &mut BinaryHeap<T>) -> Self {
        // SAFETY: The heap reference is casted to a vector to allow multiple mutable references to
        // the heap. However, the heap exists for the lifetime of the iterator, so the heap will not
        // be dropped while the iterator is still alive.
        let ptr = heap as *mut BinaryHeap<T>;
        #[allow(clippy::unwrap_used)]
        let mut data = (0..heap.len())
            .map(|i| PeekMut::new(unsafe { &mut *ptr }, i))
            .collect::<Vec<_>>();
        data.sort_by(|a, b| (heap.function)(b, a)); // The function is reversed to sort the elements in the correct order.
        BinaryHeapIterMut { data }
    }
}

impl<'a, T> Iterator for BinaryHeapIterMut<'a, T>
where
    T: 'a + Ord,
{
    type Item = PeekMut<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.data.pop()
    }
}

impl<'a, T> Iterators<'a, T> for BinaryHeap<T>
where
    T: 'a + Ord,
{
    type ItemRef = &'a T;
    type ItemMut = PeekMut<'a, T>;

    type Iter = std::vec::IntoIter<&'a T>;
    type IterMut = BinaryHeapIterMut<'a, T>;

    fn iter(&'a self) -> Self::Iter {
        let mut heap_tree: Vec<&'a T> = self.data.iter().collect();
        heap_tree.sort_by(|&a, &b| (self.function)(a, b));
        heap_tree.into_iter()
    }

    fn iter_mut(&'a mut self) -> Self::IterMut {
        BinaryHeapIterMut::new(self)
    }
}

impl<'a, T> IntoIterator for &'a BinaryHeap<T>
where
    T: 'a + Ord,
{
    type Item = &'a T;
    type IntoIter = std::vec::IntoIter<&'a T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut BinaryHeap<T>
where
    T: 'a + Ord,
{
    type Item = PeekMut<'a, T>;
    type IntoIter = BinaryHeapIterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// Returns the index of the parent of the element at the given index.
///
/// # Safety
/// The index must be greater than 0, meaning the root of the heap should never be passed to this
/// function.
const fn parent(index: usize) -> usize {
    (index - 1) / 2
}

/// Returns a tuple containing the index of the left child and the right child of the element at the
/// given index.
const fn children(index: usize) -> (usize, usize) {
    (index * 2 + 1, index * 2 + 2)
}

impl<T> BinaryHeap<T>
where
    T: Ord,
{
    /// Creates a new [`BinaryHeap`] with the given capacity, expansion mode and function that
    /// determines the order of the elements in the heap. The root of the heap is the element that
    /// has `Ordering::Less` when compared to the other elements in the heap.
    ///
    /// This a generic constructor, if you want a [`max_heap`] or a [`min_heap`], use the
    /// corresponding functions.
    ///
    /// # Panics
    /// This function panics if the capacity is 0.
    ///
    /// # Examples
    /// ```
    /// use trait_based_collection::{prelude::*, BinaryHeap};
    ///
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::new(10,
    ///                                                 ExpansionMode::Ignore,
    ///                                                 |a, b| a.cmp(b));  // Min-heap.
    /// ```
    ///
    /// [`max_heap`]: BinaryHeap::max_heap
    /// [`min_heap`]: BinaryHeap::min_heap
    #[must_use]
    pub fn new(capacity: usize, mode: ExpansionMode, function: fn(&T, &T) -> Ordering) -> Self {
        assert_ne!(capacity, 0, "Capacity must be greater than 0");
        Self {
            data: Vec::with_capacity(capacity),
            mode,
            function,
        }
    }

    /// Creates a `MinHeap` with the given capacity and expansion mode.
    ///
    /// # Panics
    /// This function panics if the capacity is 0.
    ///
    /// # Examples
    /// ```
    /// use trait_based_collection::{prelude::*, BinaryHeap};
    ///
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::min_heap(10, ExpansionMode::Overwrite);
    /// ```
    #[must_use]
    pub fn min_heap(capacity: usize, mode: ExpansionMode) -> Self {
        Self::new(capacity, mode, Ord::cmp)
    }

    /// Creates a `MaxHeap` with the given capacity and expansion mode.
    ///
    /// # Panics
    /// This function panics if the capacity is 0.
    ///
    /// # Examples
    /// ```
    /// use trait_based_collection::{prelude::*, BinaryHeap};
    ///
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::max_heap(10, ExpansionMode::Overwrite);
    /// ```
    #[must_use]
    pub fn max_heap(capacity: usize, mode: ExpansionMode) -> Self {
        Self::new(capacity, mode, |a, b| b.cmp(a))
    }

    /// Iterates down the heap, swapping the elements with their children until the heap property is
    /// satisfied. This function is called when an element is removed from the heap or when the
    /// element at the given index is modified with a greater value.
    fn heapify_down(&mut self, mut index: usize) {
        while index < self.len() {
            let (left, right) = children(index);
            let mut min = index;
            for child in [left, right] {
                if child >= self.len() {
                    // If left is out of bounds, right is also out of bounds.
                    break;
                }
                if (self.function)(&self.data[child], &self.data[min]) == Ordering::Less {
                    min = child;
                }
            }
            if min == index {
                break; // The element is in the correct position.
            }
            self.data.swap(index, min);
            index = min; // Continue heapifying from the child.
        }
    }

    /// Iterates up the heap, swapping the elements with their parent until the heap property is
    /// satisfied. This function is called when an element is inserted into the heap or when the
    /// element at the given index is modified with a smaller value.
    fn heapify_up(&mut self, mut index: usize) {
        while index > 0
            && (self.function)(&self.data[parent(index)], &self.data[index]) == Ordering::Greater
        {
            let parent = parent(index);
            self.data.swap(parent, index);
            index = parent;
        }
    }

    /// Heapifies the element independently of the element's value. This function can be called
    /// any time to ensure the heap property is satisfied. This function is called when an element
    /// is updated in the heap. For more information, see the documentation of the [`heapify_up`]
    /// and [`heapify_down`] functions.
    ///
    /// [`heapify_up`]: BinaryHeap::heapify_up
    /// [`heapify_down`]: BinaryHeap::heapify_down
    fn heapify_both(&mut self, index: usize) {
        if index == 0 {
            self.heapify_down(index);
            return;
        }
        if (self.function)(&self.data[parent(index)], &self.data[index]) == Ordering::Less {
            self.heapify_down(index);
        } else {
            // heapify_up is faster than heapify_down.
            self.heapify_up(index);
        }
    }
}

impl<'a, T> Collection<'a, T> for BinaryHeap<T>
where
    T: 'a + Ord,
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
        self.data.push(value);

        self.heapify_up(self.data.len() - 1);
    }

    fn remove(&mut self) -> Option<T> {
        if self.data.is_empty() {
            return None;
        }

        let len = self.data.len();
        self.data.swap(0, len - 1);
        let value = self.data.pop().expect("Should never fail");

        self.heapify_down(0);
        Some(value)
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    fn peek(&'a self) -> Option<Self::ItemRef> {
        self.data.first()
    }

    fn peek_mut(&'a mut self) -> Option<Self::ItemMut> {
        if self.data.is_empty() {
            None
        } else {
            Some(PeekMut::new(self, 0))
        }
    }

    fn len(&self) -> usize {
        self.data.len()
    }
}

impl<'a, T> FixedSizeCollection<'a, T> for BinaryHeap<T>
where
    T: 'a + Ord,
{
    fn with_mode(capacity: usize, mode: ExpansionMode) -> Self {
        assert_ne!(capacity, 0, "Capacity must be greater than 0");
        Self::min_heap(capacity, mode)
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

#[cfg(test)]
mod heap_tests {
    use super::*;
    use trait_based_collection_macros::test_collection;

    #[test_collection(BinaryHeap)]
    fn test_add<C: Collection<usize>>(mut heap: C) {
        for i in (0..5).rev() {
            heap.add(i);
        }
        for i in 0..5 {
            heap.add(i);
        }
    }

    #[test_collection(BinaryHeap)]
    fn test_remove<C: Collection<usize>>(mut heap: C) {
        let mut values = [2, 4, 1, 3, 5];

        assert_eq!(heap.remove(), None);
        for i in values.clone() {
            heap.add(i);
        }
        values.sort_unstable();
        for i in values {
            assert_eq!(heap.remove(), Some(i));
        }
        assert_eq!(heap.remove(), None);
    }

    #[test_collection(BinaryHeap)]
    fn test_clear<C: Collection<usize>>(mut heap: C) {
        for i in 0..5 {
            heap.add(i);
        }
        heap.clear();

        assert_eq!(heap.len(), 0);
        assert!(heap.is_empty());
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.remove(), None);
    }

    #[test_collection(BinaryHeap)]
    fn test_peek<C: Collection<usize>>(mut heap: C) {
        let mut values = [3, 1, 2, 4, 0];

        assert_eq!(heap.peek(), None);
        let mut min = usize::MAX;
        for i in values.clone() {
            heap.add(i);
            if i < min {
                min = i;
            }
            assert_eq!(heap.peek(), Some(&min));
        }
        values.sort_unstable();
        for i in values {
            assert_eq!(heap.peek(), Some(&i));
            heap.remove();
        }
        assert_eq!(heap.peek(), None);
    }

    #[test_collection(BinaryHeap)]
    fn test_peek_mut<C: Collection<usize>>(mut heap: C) {
        let mut values = [1, 4, 2, 0, 3];

        assert_eq!(heap.peek_mut(), None);
        let mut min = usize::MAX;
        for i in values.clone() {
            heap.add(i);
            if i < min {
                min = i;
            }
            let mut peek = heap.peek_mut().unwrap();
            *peek += 5;
            drop(peek);
            assert_eq!(heap.peek(), Some(&(min + 5)));
        }
        values.sort_unstable();
        for i in values {
            assert_eq!(heap.peek(), Some(&(i + 5)));
            heap.remove();
        }
        assert_eq!(heap.peek(), None);
    }

    #[test_collection(BinaryHeap)]
    fn test_get<C: Collection<usize>>(mut heap: C) {
        let mut values = [3, 0, 2, 4, 1];

        for i in values.clone() {
            heap.add(i);
        }
        values.sort_unstable();
        for (i, value) in values.into_iter().enumerate() {
            assert_eq!(heap.get(i), Some(&value));
        }
        assert_eq!(heap.get(6), None);
    }

    #[test_collection(BinaryHeap)]
    fn test_get_mut<C: Collection<usize>>(mut heap: C) {
        let mut values = [0, 2, 1, 3, 4];

        for i in values.clone() {
            heap.add(i);
        }
        for _ in 0..values.len() {
            let mut get = heap.get_mut(0).unwrap();
            *get += 10;
        }
        assert_eq!(heap.get_mut(6), None);

        values.sort_unstable();
        for (i, value) in values.into_iter().enumerate() {
            assert_eq!(heap.get(i), Some(&(value + 10)));
        }
        assert_eq!(heap.get(6), None);
    }

    #[test_collection(BinaryHeap)]
    fn test_find<C: Collection<usize>>(mut heap: C) {
        let mut values = [3, 0, 2, 4, 1];

        for i in values.clone() {
            heap.add(i);
        }
        values.sort_unstable();
        for (i, value) in values.into_iter().enumerate() {
            assert_eq!(heap.find(&value), Some(i));
        }
        assert_eq!(heap.find(&6), None);
    }

    #[test_collection(BinaryHeap)]
    fn test_contains<C: Collection<usize>>(mut heap: C) {
        for i in (0..5).rev() {
            heap.add(i);
        }
        for i in 0..5 {
            assert!(heap.contains(&i));
        }
        assert!(!heap.contains(&6));
    }

    #[test_collection(BinaryHeap)]
    fn test_len<C: Collection<usize>>(mut heap: C) {
        assert_eq!(heap.len(), 0);
        for i in (0..5).rev() {
            heap.add(i);
            assert_eq!(heap.len(), 5 - i);
        }
        assert_eq!(heap.len(), 5);
        for i in (0..5_usize).rev() {
            heap.remove();
            assert_eq!(heap.len(), i);
        }
    }

    #[test_collection(BinaryHeap)]
    fn test_is_empty<C: Collection<usize>>(mut heap: C) {
        assert!(heap.is_empty());
        for i in (0..5).rev() {
            heap.add(i);
            assert!(!heap.is_empty());
        }
        for i in 0..5 {
            heap.remove();
            assert_eq!(heap.is_empty(), i == 4);
        }
    }

    #[test_collection(BinaryHeap)]
    fn basic_test_heap<C: Collection<usize>>(mut heap: C) {
        for i in [9, 1, 8, 2, 7, 3, 6, 4, 5, 0] {
            heap.add(i);
        }
        for i in 0..10 {
            assert_eq!(heap.len(), 10 - i);
            assert!(!heap.is_empty());

            assert_eq!(heap.peek(), Some(&i));
            assert_eq!(*heap.peek_mut().unwrap(), i);

            match heap.get(1) {
                Some(x) => assert_eq!(*x, i + 1),
                None => assert_eq!(i, 9),
            }
            match heap.get_mut(1) {
                Some(x) => assert_eq!(*x, i + 1),
                None => assert_eq!(i, 9),
            }

            assert_eq!(heap.find(&i), Some(0));
            assert!(heap.contains(&i));

            assert_eq!(heap.remove(), Some(i));
        }

        assert_eq!(heap.len(), 0);
        assert!(heap.is_empty());

        assert_eq!(heap.peek(), None);
        assert_eq!(heap.peek_mut(), None);

        assert_eq!(heap.get(2), None);
        assert_eq!(heap.get_mut(2), None);

        assert_eq!(heap.find(&0), None);
        assert!(!heap.contains(&0));

        assert_eq!(heap.remove(), None);

        for i in 0..10 {
            heap.add(i);
        }
        heap.clear();

        assert_eq!(heap.len(), 0);
        assert!(heap.is_empty());

        assert_eq!(heap.peek(), None);
        assert_eq!(heap.peek_mut(), None);

        assert_eq!(heap.get(2), None);
        assert_eq!(heap.get_mut(2), None);

        assert_eq!(heap.find(&0), None);
        assert!(!heap.contains(&0));

        assert_eq!(heap.remove(), None);
    }

    #[test_collection(BinaryHeap)]
    fn test_from_iter<C: Collection<usize>>(mut _heap: C) {
        let mut heap: C<usize> = vec![5, 3, 1, 2, 4].into_iter().collect();

        assert_eq!(heap.len(), 5);
        assert!(!heap.is_empty());
        assert_eq!(heap.peek(), Some(&1));

        for i in 1..6_usize {
            assert_eq!(heap.remove(), Some(i));
        }
    }

    #[test_collection(BinaryHeap)]
    fn test_into_iter<C: Collection<usize> + Iterators<usize>>(_heap: C) {
        let mut heap: C<usize> = vec![4, 2, 0, 1, 3].into_iter().collect();

        for (i, &elem) in heap.iter().enumerate() {
            assert_eq!(elem, i);
        }
        let mut i = 0;
        for elem in &heap {
            assert_eq!(*elem, i);
            i += 1;
        }

        for (i, mut elem) in heap.iter_mut().enumerate() {
            *elem %= 3;
            assert_eq!(*elem, i % 3);
        }
        // Small test to ensure heap is reordered after mutating elements.
        heap.iter().fold(0, |prev, elem| {
            assert!(prev <= *elem);
            *elem
        });

        let mut heap: C<usize> = vec![14, 12, 10, 11, 13].into_iter().collect();
        let mut i = 10;
        for mut elem in &mut heap {
            if *elem == 13 {
                *elem = 1;
            }
            assert_eq!(*elem, if i == 13 { 1 } else { i });
            i += 1;
        }
        assert_eq!(heap.peek(), Some(&1));

        let heap: C<usize> = vec![1, 5, 2, 4, 3].into_iter().collect();
        for (i, elem) in heap.into_iter().enumerate() {
            assert_eq!(elem, i + 1);
        }
    }

    #[test]
    fn test_macro_heap() {
        // No args
        let mut heap = binary_heap![];
        heap.add(1);
        assert_eq!(heap.remove(), Some(1));

        // List of args
        let mut heap = binary_heap![1, 2, 3, 4, 5];
        assert_eq!(heap.len(), 5);
        assert!(!heap.is_empty());
        assert_eq!(heap.peek(), Some(&1));

        for i in 1..6 {
            assert_eq!(heap.remove(), Some(i));
        }

        // Arg and number of args
        let mut heap = binary_heap![1; 5];
        assert_eq!(heap.len(), 5);
        assert!(!heap.is_empty());
        assert_eq!(heap.peek(), Some(&1));

        for _ in 0..5 {
            assert_eq!(heap.remove(), Some(1));
        }
    }
}
