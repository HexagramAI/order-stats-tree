use std::collections::VecDeque;
use std::collections::vec_deque::Iter;
use rand::{RngCore, thread_rng};
use order_stats_tree2::OSTree;

fn main() {
  // simple();
  check_correct();
}

fn check_correct() {
  let mut roll_q = RollingQuantile::with_capacity(1024);
  let mut buff = VecDeque::with_capacity(10);
  let mut rng = thread_rng();
  let mut num_wrong = 0;
  for i in 0..100000 {
    let next = rng.next_u64();
    roll_q.push_back(next);
    if roll_q.len() > 7 {
      roll_q.pop_front();
    }

    buff.push_back(next);
    if buff.len() > 7 {
      buff.pop_front();
    }

    if buff.len() >= 7 {
      let x = roll_q.quantile(0.6);

      let mut tmp: Vec<_> = buff.iter().map(|e| *e).collect();
      tmp.sort();
      let y = tmp[4];
      if x != y {
        num_wrong += 1;
      }
      println!("{} == {}", x, y);
    }
  }
  println!("{:?}", roll_q.last_n(4));
  println!("#wrong: {}", num_wrong);
}

fn simple() {
  let mut a = OSTree::new();

  // for j in 0..100 {
  //   let k = j;
  //   a.increase(k, j+1);
  // }
  // for idx in 0..100 {
  //   println!("{}th: {:?}", idx, a.select(idx));
  // }

  for i in 0..1000 {
    for j in 0..100 {
      let k = i * 100 + j;
      a.increase(k, j+1);
    }
    let t10 = a.select(10);
    println!("10th: {:?}", t10);
    for j in 0..100 {
      let k = i * 100 + j;
      a.decrease(&k, j+1);
    }
  }
}

pub struct RollingQuantile {
  history: VecDeque<u64>,
  sorted_tree: OSTree<u64>,
}

impl RollingQuantile {
  pub fn with_capacity(capacity: usize) -> Self {
    let history = VecDeque::with_capacity(capacity);
    let sorted_tree = OSTree::new();
    RollingQuantile { history, sorted_tree }
  }

  pub fn last_n(&self, n: usize) -> Iter<'_, u64> {
    let len = self.history.len();
    let s = if len >= n { len - n } else { 0 };
    self.history.range(s..)
  }

  pub fn debug_last_n(&self, n: usize) -> String {
    use std::fmt::Write;

    let mut result = String::with_capacity(n*8);
    result.push_str("[");
    let len = self.history.len();
    let s = if len >= n { len - n } else { 0 };
    for s in self.history.range(s..) {
      write!(&mut result, "{}", s).unwrap();
      result.push_str(",");
    }
    result.push_str("]");
    result
  }

  #[inline(always)]
  pub fn last(&self) -> Option<u64> {
    self.history.back().map(|f| *f)
  }

  #[inline(always)]
  pub fn quantile(&self, pct: f64) -> u64 {
    if self.history.is_empty() {
      0
    } else {
      let index = (pct * self.len() as f64).round() as usize;
      let index = index.min(self.len() - 1);
      self.sorted_tree.select(index).map(|(k, _)| k).unwrap()
    }
  }

  #[inline(always)]
  pub fn len(&self) -> usize {
    self.history.len()
  }

  #[inline(always)]
  pub fn push_back(&mut self, value: u64) {
    self.sorted_tree.increase(value, 1);
    self.history.push_back(value);
  }

  #[inline(always)]
  pub fn pop_front(&mut self) {
    if let Some(old_val) = self.history.pop_front() {
      self.sorted_tree.decrease(&old_val, 1);
    }
  }
}