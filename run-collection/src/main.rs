#[allow(dead_code, unused_imports)]
use trait_based_collection::{import, CircularDeque};
import!();

fn main() {
    let mut queue: CircularDeque<i32> = circular_deque![1, 2, 3, 4, 5];
    queue[2] = 10;
    for i in &mut queue {
        println!("{}", i);
    }
}
