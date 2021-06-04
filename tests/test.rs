use order_stats_tree::OSTree;

#[test]
fn test_increase() {
    let mut m = OSTree::new();
    assert_eq!(m.len(), 0);
    m.increase(1, 2);
    assert_eq!(m.len(), 2);
    m.increase(2, 4);
    assert_eq!(m.len(), 6);
    m.increase(3, 6);
    assert_eq!(m.len(), 12);

    assert_eq!(m.count(&1).unwrap(), 2);
    assert_eq!(m.count(&2).unwrap(), 4);
    assert_eq!(m.count(&3).unwrap(), 6);
}

#[test]
fn test_increase_with_exist() {
    let mut m = OSTree::new();
    assert_eq!(m.len(), 0);
    m.increase(1, 2);
    assert_eq!(m.len(), 2);
    m.increase(2, 4);
    assert_eq!(m.len(), 6);
    m.increase(2, 6);
    assert_eq!(m.len(), 12);

    assert_eq!(m.count(&1).unwrap(), 2);
    assert_eq!(m.count(&2).unwrap(), 10);
}

#[test]
fn test_increase_decrease() {
    let mut m = OSTree::new();
    assert_eq!(m.len(), 0);
    m.increase(1, 2);
    m.increase(2, 4);
    m.increase(3, 6);
    m.print_tree();
    m.decrease(&3, 1);
    m.print_tree();
    assert_eq!(m.len(), 11);
    assert_eq!(m.count(&3).unwrap(), 5);

    m.decrease(&3, 5);
    assert_eq!(m.len(), 6);
    assert!(m.count(&3).is_none());
}

#[test]
fn test_clone() {
    let mut m = OSTree::new();
    assert_eq!(m.len(), 0);
    m.increase(1, 1);
    assert_eq!(m.len(), 1);
    m.increase(2, 2);
    assert_eq!(m.len(), 3);
    let m2 = m.clone();
    m.clear();
    assert_eq!(m2.count(&1).unwrap(), 1);
    assert_eq!(m2.count(&2).unwrap(), 2);
    assert_eq!(m2.len(), 3);
}

#[test]
fn test_empty_remove() {
    let mut m: OSTree<isize> = OSTree::new();
    assert_eq!(m.remove(&0), None);
}

#[test]
fn test_empty_decrease() {
    let mut m: OSTree<isize> = OSTree::new();
    assert_eq!(m.decrease(&11, 3), None);
}

// #[test]
// fn test_empty_iter() {
//     let mut m: OSTree<isize, bool> = OSTree::new();
//     assert_eq!(m.iter().next(), None);
//     assert_eq!(m.iter_mut().next(), None);
//     assert_eq!(m.len(), 0);
//     assert!(m.is_empty());
//     assert_eq!(m.into_iter().next(), None);
// }

// #[test]
// fn test_lots_of_insertions() {
//     let mut m = OSTree::new();

//     // Try this a few times to make sure we never screw up the hashmap's
//     // internal state.
//     for _ in 0..10 {
//         assert!(m.is_empty());

//         for i in 1..101 {
//             m.insert(i, i);

//             for j in 1..i + 1 {
//                 let r = m.get_count(&j);
//                 assert_eq!(r, Some(&j));
//             }

//             for j in i + 1..101 {
//                 let r = m.get_count(&j);
//                 assert_eq!(r, None);
//             }
//         }

//         for i in 101..201 {
//             assert!(!m.contains_key(&i));
//         }

//         // remove forwards
//         for i in 1..101 {
//             assert!(m.remove(&i).is_some());

//             for j in 1..i + 1 {
//                 assert!(!m.contains_key(&j));
//             }

//             for j in i + 1..101 {
//                 assert!(m.contains_key(&j));
//             }
//         }

//         for i in 1..101 {
//             assert!(!m.contains_key(&i));
//         }

//         for i in 1..101 {
//             m.insert(i, i);
//         }

//         // remove backwards
//         for i in (1..101).rev() {
//             assert!(m.remove(&i).is_some());

//             for j in i..101 {
//                 assert!(!m.contains_key(&j));
//             }

//             for j in 1..i {
//                 assert!(m.contains_key(&j));
//             }
//         }
//     }
// }

#[test]
fn test_remove() {
    let mut m = OSTree::new();
    m.increase(1, 2);
    assert_eq!(m.count(&1).unwrap(), 2);
    m.increase(5, 3);
    assert_eq!(m.count(&5).unwrap(), 3);
    m.increase(9, 4);
    assert_eq!(m.count(&1).unwrap(), 2);
    assert_eq!(m.count(&5).unwrap(), 3);
    assert_eq!(m.count(&9).unwrap(), 4);
    assert_eq!(m.remove(&1).unwrap(), 2);
    assert_eq!(m.remove(&5).unwrap(), 3);
    assert_eq!(m.remove(&9).unwrap(), 4);
    assert_eq!(m.len(), 0);
}

#[test]
fn test_is_empty_remove() {
    let mut m = OSTree::new();
    m.increase(1, 2);
    assert!(!m.is_empty());
    assert!(m.remove(&1).is_some());
    assert!(m.is_empty());
}

#[test]
fn test_is_empty_decrease() {
    let mut m = OSTree::new();
    m.increase(1, 2);
    assert!(!m.is_empty());
    assert!(m.decrease(&1, 1).is_some());
    assert!(m.decrease(&1, 1).is_some());
    assert!(m.is_empty());
}

#[test]
fn test_pop() {
    let mut m = OSTree::new();
    m.increase(2, 4);
    m.increase(1, 2);
    m.increase(3, 6);
    assert_eq!(m.len(), 12);
    assert_eq!(m.pop_first(), Some((1, 2)));
    assert_eq!(m.len(), 10);
    assert_eq!(m.pop_last(), Some((3, 6)));
    assert_eq!(m.len(), 4);
    assert_eq!(m.get_first(), Some((2, 4)));
    assert_eq!(m.get_last(), Some((2, 4)));
}

// #[test]
// fn test_iterate() {
//     let mut m = OSTree::new();
//     for i in 0..32 {
//         m.insert(i, i * 2);
//     }
//     assert_eq!(m.len(), 32);

//     let mut observed: u32 = 0;

//     for (k, v) in m.iter() {
//         assert_eq!(*v, *k * 2);
//         observed |= 1 << *k;
//     }
//     assert_eq!(observed, 0xFFFF_FFFF);
// }

// #[test]
// fn test_keys() {
//     let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
//     let map: OSTree<_, _> = vec.into_iter().collect();
//     let keys: Vec<_> = map.keys().cloned().collect();
//     assert_eq!(keys.len(), 3);
//     assert!(keys.contains(&1));
//     assert!(keys.contains(&2));
//     assert!(keys.contains(&3));
// }

// #[test]
// fn test_values() {
//     let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
//     let map: OSTree<_, _> = vec.into_iter().collect();
//     let values: Vec<_> = map.values().cloned().collect();
//     assert_eq!(values.len(), 3);
//     assert!(values.contains(&'a'));
//     assert!(values.contains(&'b'));
//     assert!(values.contains(&'c'));
// }

// #[test]
// fn test_values_mut() {
//     let vec = vec![(1, 1), (2, 2), (3, 3)];
//     let mut map: OSTree<_, _> = vec.into_iter().collect();
//     for value in map.values_mut() {
//         *value = (*value) * 2
//     }
//     let values: Vec<_> = map.values().cloned().collect();
//     assert_eq!(values.len(), 3);
//     assert!(values.contains(&2));
//     assert!(values.contains(&4));
//     assert!(values.contains(&6));
// }

// #[test]
// fn test_find() {
//     let mut m = OSTree::new();
//     assert!(m.get_count(&1).is_none());
//     m.insert(1, 2);
//     match m.get_count(&1) {
//         None => panic!(),
//         Some(v) => assert_eq!(*v, 2),
//     }
// }

// #[test]
// fn test_eq() {
//     let mut m1 = OSTree::new();
//     m1.insert(1, 2);
//     m1.insert(2, 3);
//     m1.insert(3, 4);

//     let mut m2 = OSTree::new();
//     m2.insert(1, 2);
//     m2.insert(2, 3);

//     assert!(m1 != m2);

//     m2.insert(3, 4);

//     assert_eq!(m1, m2);
// }

// #[test]
// fn test_show() {
//     let mut map = OSTree::new();
//     let empty: OSTree<i32, i32> = OSTree::new();

//     map.insert(1, 2);
//     map.insert(3, 4);

//     let map_str = format!("{:?}", map);

//     assert!(map_str == "{1: 2, 3: 4}" || map_str == "{3: 4, 1: 2}");
//     assert_eq!(format!("{:?}", empty), "{}");
// }

// #[test]
// fn test_from_iter() {
//     let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

//     let map: OSTree<_, _> = xs.iter().cloned().collect();

//     for &(k, v) in &xs {
//         assert_eq!(map.get_count(&k), Some(&v));
//     }
// }

// #[test]
// fn test_size_hint() {
//     let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

//     let map: OSTree<_, _> = xs.iter().cloned().collect();

//     let mut iter = map.iter();

//     for _ in iter.by_ref().take(3) {}

//     assert_eq!(iter.size_hint(), (3, Some(3)));
// }

// #[test]
// fn test_iter_len() {
//     let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

//     let map: OSTree<_, _> = xs.iter().cloned().collect();

//     let mut iter = map.iter();

//     for _ in iter.by_ref().take(3) {}

//     assert_eq!(iter.count(), 3);
// }

// #[test]
// fn test_mut_size_hint() {
//     let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

//     let mut map: OSTree<_, _> = xs.iter().cloned().collect();

//     let mut iter = map.iter_mut();

//     for _ in iter.by_ref().take(3) {}

//     assert_eq!(iter.size_hint(), (3, Some(3)));
// }

// #[test]
// fn test_iter_mut_len() {
//     let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

//     let mut map: OSTree<_, _> = xs.iter().cloned().collect();

//     let mut iter = map.iter_mut();

//     for _ in iter.by_ref().take(3) {}

//     assert_eq!(iter.count(), 3);
// }

// #[test]
// fn test_index() {
//     let mut map = OSTree::new();

//     map.insert(1, 2);
//     map.insert(2, 1);
//     map.insert(3, 4);

//     assert_eq!(map[&2], 1);
// }

#[test]
#[should_panic]
fn test_index_nonexistent() {
    let mut map = OSTree::new();

    map.increase(1, 2);
    map.increase(2, 1);
    map.increase(3, 4);

    map.count(&4).unwrap();
}

// #[test]
// fn test_extend_iter() {
//     let mut a = OSTree::new();
//     a.insert(1, "one");
//     let mut b = OSTree::new();
//     b.insert(2, "two");
//     b.insert(3, "three");

//     a.extend(b.into_iter());

//     assert_eq!(a.len(), 3);
//     assert_eq!(a[&1], "one");
//     assert_eq!(a[&2], "two");
//     assert_eq!(a[&3], "three");
// }

#[test]
fn test_rank() {
    let mut a = OSTree::new();
    a.increase(1, 1);
    a.increase(2, 1);
    a.increase(4, 1);
    a.increase(3, 1);
    a.increase(11, 1);
    a.increase(9, 1);
    a.increase(7, 1);
    a.remove(&2);
    a.remove(&11);

    assert_eq!(a.rank(&99), None);
    a.print_tree();
    assert_eq!(a.rank(&9).unwrap(), 4);
    assert_eq!(a.rank(&7).unwrap(), 3);
    assert_eq!(a.rank(&4).unwrap(), 2);
    assert_eq!(a.rank(&3).unwrap(), 1);
    assert_eq!(a.rank(&1).unwrap(), 0);
}

#[test]
fn test_select() {
    let mut a = OSTree::new();
    a.increase(1, 1);
    a.increase(2, 2);
    a.increase(4, 1);
    a.increase(3, 1);
    a.increase(11, 1);
    a.increase(9, 1);
    a.increase(7, 1);
    a.remove(&2);
    a.remove(&11);

    a.print_tree();
    assert_eq!(a.select(99), None);
    assert_eq!(a.select(4).unwrap().0, 9);
    assert_eq!(a.select(3).unwrap().0, 7);
    assert_eq!(a.select(2).unwrap().0, 4);
    assert_eq!(a.select(1).unwrap().0, 3);
    assert_eq!(a.select(0).unwrap().0, 1);
}
