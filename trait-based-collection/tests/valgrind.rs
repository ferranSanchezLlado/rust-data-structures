use trait_based_collection::{
    ArrayStack, BinaryHeap, CircularDeque, Collection, Deque, Queue, Stack,
};
use trait_based_collection_macros::test_collection;

#[test_collection(ArrayStack, BinaryHeap, CircularDeque, Deque, Queue, Stack; ignore)]
fn valgrind_test<C: Collection<i32>>(mut collection: C) {
    for i in 0..10 {
        collection.add(i);

        collection.len();
        collection.is_empty();
        collection.peek();
    }
    for _ in 0..10 {
        collection.len();
        collection.is_empty();
        collection.peek();

        collection.remove();
    }
    collection.len();
    collection.is_empty();
    collection.peek();
    collection.remove();

    for i in 0..10 {
        collection.add(i);

        collection.len();
        collection.is_empty();
        collection.peek();
    }
    collection.clear();

    collection.len();
    collection.is_empty();
    collection.peek();
    collection.remove();
}

// TODO: Test for FixedCollection
