use rand::random;
use std::collections::VecDeque;

// for easy memory check using valgrind
fn main() {
    let mut tree = order_stats_tree::OSTree::new();

    let wsize = 320;

    let mut history = VecDeque::new();
    let mut result = vec![];

    for _ in 0..100000 {
        let x: u8 = random();
        history.push_back(x);
        tree.increase(x, 1);

        let rank = tree.rank(&x).unwrap();
        result.push(rank);

        if history.len() > wsize {
            let r = history.pop_front().unwrap();
            tree.increase(r, 1);
        }
    }
    drop(tree);
}
