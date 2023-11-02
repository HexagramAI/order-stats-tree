use order_stats_tree::OSTree;

fn main() {
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