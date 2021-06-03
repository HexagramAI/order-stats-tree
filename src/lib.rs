// Copyright 2017-2018 By tickdream125@hotmail.com.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cmp::Ord;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::iter::{FromIterator, IntoIterator};
use std::marker;
use std::mem;
use std::ops::Index;
use std::ptr;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

/*****************OSTreeNode***************************/
struct OSTreeNode<K: Ord, V> {
    color: Color,
    left: NodePtr<K, V>,
    right: NodePtr<K, V>,
    parent: NodePtr<K, V>,
    key: K,
    value: V,
    size: usize, // size[x] = size[left[x]] + size[right[x]] + 1
}

impl<K: Ord, V> OSTreeNode<K, V> {
    #[inline]
    fn pair(self) -> (K, V) {
        (self.key, self.value)
    }
}

impl<K, V> Debug for OSTreeNode<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "k:{:?} v:{:?} c:{:?}", self.key, self.value, self.color)
    }
}

/*****************NodePtr***************************/
#[derive(Debug)]
struct NodePtr<K: Ord, V>(*mut OSTreeNode<K, V>);

impl<K: Ord, V> Clone for NodePtr<K, V> {
    fn clone(&self) -> NodePtr<K, V> {
        NodePtr(self.0)
    }
}

impl<K: Ord, V> Copy for NodePtr<K, V> {}

impl<K: Ord, V> Ord for NodePtr<K, V> {
    fn cmp(&self, other: &NodePtr<K, V>) -> Ordering {
        unsafe { (*self.0).key.cmp(&(*other.0).key) }
    }
}

impl<K: Ord, V> PartialOrd for NodePtr<K, V> {
    fn partial_cmp(&self, other: &NodePtr<K, V>) -> Option<Ordering> {
        unsafe { Some((*self.0).key.cmp(&(*other.0).key)) }
    }
}

impl<K: Ord, V> PartialEq for NodePtr<K, V> {
    fn eq(&self, other: &NodePtr<K, V>) -> bool {
        self.0 == other.0
    }
}

impl<K: Ord, V> Eq for NodePtr<K, V> {}

impl<K: Ord, V> NodePtr<K, V> {
    fn new(k: K, v: V) -> NodePtr<K, V> {
        let node = OSTreeNode {
            color: Color::Black,
            left: NodePtr::null(),
            right: NodePtr::null(),
            parent: NodePtr::null(),
            key: k,
            value: v,
            size: 1,
        };
        NodePtr(Box::into_raw(Box::new(node)))
    }

    #[inline]
    fn set_color(&mut self, color: Color) {
        if self.is_null() {
            return;
        }
        unsafe {
            (*self.0).color = color;
        }
    }

    #[inline]
    fn set_red_color(&mut self) {
        self.set_color(Color::Red);
    }

    #[inline]
    fn set_black_color(&mut self) {
        self.set_color(Color::Black);
    }

    #[inline]
    fn get_color(&self) -> Color {
        if self.is_null() {
            return Color::Black;
        }
        unsafe { (*self.0).color }
    }

    #[inline]
    fn is_red_color(&self) -> bool {
        if self.is_null() {
            return false;
        }
        unsafe { (*self.0).color == Color::Red }
    }

    #[inline]
    fn is_black_color(&self) -> bool {
        if self.is_null() {
            return true;
        }
        unsafe { (*self.0).color == Color::Black }
    }

    #[inline]
    fn is_left_child(&self) -> bool {
        self.parent().left() == *self
    }

    #[inline]
    fn is_right_child(&self) -> bool {
        self.parent().right() == *self
    }

    #[inline]
    fn min_node(self) -> NodePtr<K, V> {
        let mut temp = self.clone();
        while !temp.left().is_null() {
            temp = temp.left();
        }
        return temp;
    }

    #[inline]
    fn max_node(self) -> NodePtr<K, V> {
        let mut temp = self.clone();
        while !temp.right().is_null() {
            temp = temp.right();
        }
        return temp;
    }

    #[inline]
    fn next(self) -> NodePtr<K, V> {
        if !self.right().is_null() {
            self.right().min_node()
        } else {
            let mut temp = self;
            loop {
                if temp.parent().is_null() {
                    return NodePtr::null();
                }
                if temp.is_left_child() {
                    return temp.parent();
                }
                temp = temp.parent();
            }
        }
    }

    #[inline]
    fn prev(self) -> NodePtr<K, V> {
        if !self.left().is_null() {
            self.left().max_node()
        } else {
            let mut temp = self;
            loop {
                if temp.parent().is_null() {
                    return NodePtr::null();
                }
                if temp.is_right_child() {
                    return temp.parent();
                }
                temp = temp.parent();
            }
        }
    }

    #[inline]
    fn set_parent(&mut self, parent: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).parent = parent }
    }

    #[inline]
    fn set_left(&mut self, left: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).left = left }
    }

    #[inline]
    fn set_right(&mut self, right: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).right = right }
    }

    #[inline]
    fn parent(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).parent.clone() }
    }

    #[inline]
    fn left(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).left.clone() }
    }

    #[inline]
    fn right(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).right.clone() }
    }

    #[inline]
    fn null() -> NodePtr<K, V> {
        NodePtr(ptr::null_mut())
    }

    #[inline]
    fn is_null(&self) -> bool {
        self.0.is_null()
    }

    #[inline]
    fn size(&self) -> usize {
        if self.is_null() {
            0
        } else {
            unsafe { (*self.0).size }
        }
    }

    #[inline]
    fn set_size(&self, size: usize) {
        if self.is_null() {
            return;
        } else {
            unsafe { (*self.0).size = size }
        }
    }

    #[inline]
    fn refresh_size(&self) {
        if self.is_null() {
            return;
        } else {
            self.set_size(1 + self.left().size() + self.right().size())
        }
    }

    fn select(&self, i: usize) -> Option<NodePtr<K, V>> {
        // Returns the i'th element (zero-indexed) of the elements in t

        if i >= self.size() {
            return None;
        }

        let l = self.left().size();
        if i == l {
            Some(*self)
        } else if i < l {
            self.left().select(i)
        } else {
            self.right().select(i - l - 1)
        }
    }
}

impl<K: Ord + Clone, V: Clone> NodePtr<K, V> {
    unsafe fn deep_clone(&self) -> NodePtr<K, V> {
        let mut node = NodePtr::new((*self.0).key.clone(), (*self.0).value.clone());
        if !self.left().is_null() {
            node.set_left(self.left().deep_clone());
            node.left().set_parent(node);
        }
        if !self.right().is_null() {
            node.set_right(self.right().deep_clone());
            node.right().set_parent(node);
        }
        node.refresh_size();
        node
    }
}

/// A red black tree implemented with Rust
/// It is required that the keys implement the [`Ord`] traits.

/// # Examples
/// ```rust
/// use order_stats_tree::OSTree;
/// // type inference lets us omit an explicit type signature (which
/// // would be `OSTree<&str, &str>` in this example).
/// let mut book_reviews = OSTree::new();
///
/// // review some books.
/// book_reviews.insert("Adventures of Huckleberry Finn", "My favorite book.");
/// book_reviews.insert("Grimms' Fairy Tales", "Masterpiece.");
/// book_reviews.insert("Pride and Prejudice", "Very enjoyable.");
/// book_reviews.insert("The Adventures of Sherlock Holmes", "Eye lyked it alot.");
///
/// // check for a specific one.
/// if !book_reviews.contains_key(&"Les Misérables") {
///     println!(
///         "We've got {} reviews, but Les Misérables ain't one.",
///         book_reviews.len()
///     );
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// book_reviews.remove(&"The Adventures of Sherlock Holmes");
///
/// // look up the values associated with some keys.
/// let to_find = ["Pride and Prejudice", "Alice's Adventure in Wonderland"];
/// for book in &to_find {
///     match book_reviews.get(book) {
///         Some(review) => println!("{}: {}", book, review),
///         None => println!("{} is unreviewed.", book),
///     }
/// }
///
/// // iterate over everything.
/// for (book, review) in book_reviews.iter() {
///     println!("{}: \"{}\"", book, review);
/// }
///
/// book_reviews.print_tree();
/// ```
///
/// // A `OSTree` with fixed list of elements can be initialized from an array:
///  ```
/// use order_stats_tree::OSTree;
///  let timber_resources: OSTree<&str, i32> =
///  [("Norway", 100),
///   ("Denmark", 50),
///   ("Iceland", 10)]
///   .iter().cloned().collect();
///  // use the values stored in ostree
///  ```
pub struct OSTree<K: Ord, V> {
    root: NodePtr<K, V>,
}

// Drop all owned pointers if the tree is dropped
impl<K: Ord, V> Drop for OSTree<K, V> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

/// If key and value are both impl Clone, we can call clone to get a copy.
impl<K: Ord + Clone, V: Clone> Clone for OSTree<K, V> {
    fn clone(&self) -> OSTree<K, V> {
        unsafe {
            let mut new = OSTree::new();
            new.root = self.root.deep_clone();
            new
        }
    }
}

impl<K, V> Debug for OSTree<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Ord, V> OSTree<K, V> {
    fn size(&self) -> usize {
        self.root.size()
    }

    /// Get the (key, value) of the given rank, 0 based
    /// Return None if the rank is out of range
    ///
    /// # Examples
    /// ```rust
    /// use order_stats_tree::OSTree;
    /// let mut m = OSTree::new();
    ///
    /// m.insert(1, 2);
    /// m.insert(2, 4);
    /// assert_eq!(m.select(0).unwrap(), (&1, &2));
    /// ```
    pub fn select(&self, i: usize) -> Option<(&K, &V)> {
        match self.root.select(i) {
            Some(node) => unsafe { Some((&(*node.0).key, &(*node.0).value)) },
            None => None,
        }
    }

    /// Get the rank of the element, 0 based
    /// Return None if the element is not found
    ///
    /// # Examples
    /// ```rust
    /// use order_stats_tree::OSTree;
    /// let mut m = OSTree::new();
    ///
    /// m.insert(1, 2);
    /// m.insert(2, 4);
    /// assert_eq!(m.rank(&2).unwrap(), 1);
    /// ```
    pub fn rank(&self, x: &K) -> Option<usize> {
        // Returns the position of x (one-indexed) in the linear sorted list of elements of the tree T
        let x = self.find_node(x);
        if x.is_null() {
            return None;
        }

        let mut rank = x.left().size() + 1;
        let mut y = x;
        while y != self.root {
            if y == y.parent().right() {
                rank = rank + y.parent().left().size() + 1
            }
            y = y.parent();
        }
        Some(rank - 1)
    }
}

/// This is a method to help us to get inner struct.
impl<K: Ord + Debug, V: Debug> OSTree<K, V> {
    fn tree_print(&self, node: NodePtr<K, V>, direction: i32) {
        if node.is_null() {
            return;
        }
        if direction == 0 {
            unsafe {
                println!("'{:?} ({})' is root node", (*node.0), node.size());
            }
        } else {
            let direct = if direction == -1 { "left" } else { "right" };
            unsafe {
                println!(
                    "{:?} ({}) is {:?}'s {:?} child ",
                    (*node.0),
                    node.size(),
                    *node.parent().0,
                    direct
                );
            }
        }
        self.tree_print(node.left(), -1);
        self.tree_print(node.right(), 1);
    }

    pub fn print_tree(&self) {
        if self.root.is_null() {
            println!("This is a empty tree");
            return;
        }
        println!("This tree size = {:?}, begin:-------------", self.len());
        self.tree_print(self.root, 0);
        println!("end--------------------------");
    }
}

/// all key be same, but it has multi key, if has multi key, it perhaps no correct
impl<K, V> PartialEq for OSTree<K, V>
where
    K: Eq + Ord,
    V: PartialEq,
{
    fn eq(&self, other: &OSTree<K, V>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V> Eq for OSTree<K, V>
where
    K: Eq + Ord,
    V: Eq,
{
}

impl<'a, K, V> Index<&'a K> for OSTree<K, V>
where
    K: Ord,
{
    type Output = V;

    #[inline]
    fn index(&self, index: &K) -> &V {
        self.get(index).expect("no entry found for key")
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for OSTree<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> OSTree<K, V> {
        let mut tree = OSTree::new();
        tree.extend(iter);
        tree
    }
}

/// OSTree into iter
impl<K: Ord, V> Extend<(K, V)> for OSTree<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

/// provide the ostree all keys
/// # Examples
/// ```
/// use order_stats_tree::OSTree;
/// let mut m = OSTree::new();
/// for i in 1..6 {
///     m.insert(i, i);
/// }
/// let vec = vec![1, 2, 3, 4, 5];
/// let key_vec: Vec<_> = m.keys().cloned().collect();
/// assert_eq!(vec, key_vec);
/// ```
pub struct Keys<'a, K: Ord + 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: Ord, V> Clone for Keys<'a, K, V> {
    fn clone(&self) -> Keys<'a, K, V> {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K: Ord + Debug, V> fmt::Debug for Keys<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<&'a K> {
        self.inner.next().map(|(k, _)| k)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// provide the ostree all values order by key
/// # Examples
/// ```
/// use order_stats_tree::OSTree;
/// let mut m = OSTree::new();
/// m.insert(2, 5);
/// m.insert(1, 6);
/// m.insert(3, 8);
/// m.insert(4, 9);
/// let vec = vec![6, 5, 8, 9];
/// let key_vec: Vec<_> = m.values().cloned().collect();
/// assert_eq!(vec, key_vec);
/// ```
pub struct Values<'a, K: 'a + Ord, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: Ord, V> Clone for Values<'a, K, V> {
    fn clone(&self) -> Values<'a, K, V> {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K: Ord + Debug, V: Debug> fmt::Debug for Values<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// provide the ostree all values and it can be modify
/// # Examples
/// ```
/// use order_stats_tree::OSTree;
/// let mut m = OSTree::new();
/// for i in 0..32 {
///     m.insert(i, i);
/// }
/// assert_eq!(m.len(), 32);
/// for v in m.values_mut() {
///     *v *= 2;
/// }
/// for i in 0..32 {
///     assert_eq!(m.get(&i).unwrap(), &(i * 2));
/// }
/// ```
pub struct ValuesMut<'a, K: 'a + Ord, V: 'a> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K: Ord, V> Clone for ValuesMut<'a, K, V> {
    fn clone(&self) -> ValuesMut<'a, K, V> {
        ValuesMut {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K: Ord + Debug, V: Debug> fmt::Debug for ValuesMut<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<&'a mut V> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// Convert OSTree to iter, move out the tree.
pub struct IntoIter<K: Ord, V> {
    head: NodePtr<K, V>,
    tail: NodePtr<K, V>,
    len: usize,
}

// Drop all owned pointers if the collection is dropped
impl<K: Ord, V> Drop for IntoIter<K, V> {
    #[inline]
    fn drop(&mut self) {
        for (_, _) in self {}
    }
}

impl<K: Ord, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        if self.len == 0 {
            return None;
        }

        if self.head.is_null() {
            return None;
        }

        let next = self.head.next();
        let obj = unsafe { Box::from_raw(self.head.0) };
        let (k, v) = obj.pair();
        self.head = next;
        self.len -= 1;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K: Ord, V> DoubleEndedIterator for IntoIter<K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(K, V)> {
        if self.len == 0 {
            return None;
        }

        if self.tail.is_null() {
            return None;
        }

        let prev = self.tail.prev();
        let obj = unsafe { Box::from_raw(self.tail.0) };
        let (k, v) = obj.pair();
        self.tail = prev;
        self.len -= 1;
        Some((k, v))
    }
}

/// provide iter ref for OSTree
/// # Examples
/// ```
/// use order_stats_tree::OSTree;
/// let mut m = OSTree::new();
/// for i in 0..32 {
///     m.insert(i, i * 2);
/// }
/// assert_eq!(m.len(), 32);
/// let mut observed: u32 = 0;
/// for (k, v) in m.iter() {
///     assert_eq!(*v, *k * 2);
///     observed |= 1 << *k;
/// }
/// assert_eq!(observed, 0xFFFF_FFFF);
/// ```
pub struct Iter<'a, K: Ord + 'a, V: 'a> {
    head: NodePtr<K, V>,
    tail: NodePtr<K, V>,
    len: usize,
    _marker: marker::PhantomData<&'a ()>,
}

impl<'a, K: Ord + 'a, V: 'a> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: self._marker,
        }
    }
}

impl<'a, K: Ord + 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            return None;
        }

        if self.head.is_null() {
            return None;
        }

        let (k, v) = unsafe { (&(*self.head.0).key, &(*self.head.0).value) };
        self.head = self.head.next();
        self.len -= 1;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K: Ord + 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        // println!("len = {:?}", self.len);
        if self.len == 0 {
            return None;
        }

        if self.tail == self.head {
            return None;
        }

        let (k, v) = unsafe { (&(*self.tail.0).key, &(*self.tail.0).value) };
        self.tail = self.tail.prev();
        self.len -= 1;
        Some((k, v))
    }
}

/// provide iter mut ref for OSTree
/// # Examples
/// ```
/// use order_stats_tree::OSTree;
/// let mut m = OSTree::new();
/// for i in 0..32 {
///     m.insert(i, i);
/// }
/// assert_eq!(m.len(), 32);
/// for (_, v) in m.iter_mut() {
///     *v *= 2;
/// }
/// for i in 0..32 {
///     assert_eq!(m.get(&i).unwrap(), &(i * 2));
/// }
/// ```
pub struct IterMut<'a, K: Ord + 'a, V: 'a> {
    head: NodePtr<K, V>,
    tail: NodePtr<K, V>,
    len: usize,
    _marker: marker::PhantomData<&'a ()>,
}

impl<'a, K: Ord + 'a, V: 'a> Clone for IterMut<'a, K, V> {
    fn clone(&self) -> IterMut<'a, K, V> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: self._marker,
        }
    }
}

impl<'a, K: Ord + 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        if self.head.is_null() {
            return None;
        }

        let (k, v) = unsafe { (&(*self.head.0).key, &mut (*self.head.0).value) };
        self.head = self.head.next();
        self.len -= 1;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K: Ord + 'a, V: 'a> DoubleEndedIterator for IterMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        if self.tail == self.head {
            return None;
        }

        let (k, v) = unsafe { (&(*self.tail.0).key, &mut (*self.tail.0).value) };
        self.tail = self.tail.prev();
        self.len -= 1;
        Some((k, v))
    }
}

impl<K: Ord, V> IntoIterator for OSTree<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(mut self) -> IntoIter<K, V> {
        let iter = if self.root.is_null() {
            IntoIter {
                head: NodePtr::null(),
                tail: NodePtr::null(),
                len: self.len(),
            }
        } else {
            IntoIter {
                head: self.first_child(),
                tail: self.last_child(),
                len: self.len(),
            }
        };
        self.fast_clear();
        iter
    }
}

impl<K: Ord, V> OSTree<K, V> {
    /// Creates an empty `OSTree`.
    pub fn new() -> OSTree<K, V> {
        OSTree {
            root: NodePtr::null(),
        }
    }

    /// Returns the len of `OSTree`.
    #[inline]
    pub fn len(&self) -> usize {
        self.size()
    }

    /// Returns `true` if the `OSTree` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.root.is_null()
    }

    /*
     * 对红黑树的节点(x)进行左旋转
     *
     * 左旋示意图(对节点x进行左旋)：
     *      px                              px
     *     /                               /
     *    x                               y
     *   /  \      --(左旋)-->           / \                #
     *  lx   y                          x  ry
     *     /   \                       /  \
     *    ly   ry                     lx  ly
     *
     *
     */
    #[inline]
    unsafe fn left_rotate(&mut self, mut x: NodePtr<K, V>) {
        let mut y = x.right();
        x.set_right(y.left());

        if !y.left().is_null() {
            y.left().set_parent(x.clone());
        }

        y.set_parent(x.parent());
        if x == self.root {
            self.root = y.clone();
        } else if x == x.parent().left() {
            x.parent().set_left(y.clone());
        } else {
            x.parent().set_right(y.clone());
        }

        y.set_left(x.clone());
        x.set_parent(y.clone());

        x.refresh_size();
        y.refresh_size();
    }

    /*
     * 对红黑树的节点(y)进行右旋转
     *
     * 右旋示意图(对节点y进行左旋)：
     *            py                               py
     *           /                                /
     *          y                                x
     *         /  \      --(右旋)-->            /  \                     #
     *        x   ry                           lx   y
     *       / \                                   / \                   #
     *      lx  rx                                rx  ry
     *
     */
    #[inline]
    unsafe fn right_rotate(&mut self, mut y: NodePtr<K, V>) {
        let mut x = y.left();
        y.set_left(x.right());

        if !x.right().is_null() {
            x.right().set_parent(y.clone());
        }

        x.set_parent(y.parent());
        if y == self.root {
            self.root = x.clone();
        } else if y == y.parent().right() {
            y.parent().set_right(x.clone());
        } else {
            y.parent().set_left(x.clone());
        }

        x.set_right(y.clone());
        y.set_parent(x.clone());

        y.refresh_size();
        x.refresh_size();
    }

    /// replace value if key exist, if not exist insert it.
    /// # Examples
    /// ```
    /// use order_stats_tree::OSTree;
    /// let mut m = OSTree::new();
    /// assert_eq!(m.len(), 0);
    /// m.insert(2, 4);
    /// assert_eq!(m.len(), 1);
    /// assert_eq!(m.replace_or_insert(2, 6).unwrap(), 4);
    /// assert_eq!(m.len(), 1);
    /// assert_eq!(*m.get(&2).unwrap(), 6);
    /// ```
    #[inline]
    pub fn replace_or_insert(&mut self, k: K, mut v: V) -> Option<V> {
        let node = self.find_node(&k);
        if node.is_null() {
            self.insert(k, v);
            return None;
        }

        unsafe {
            mem::swap(&mut v, &mut (*node.0).value);
        }

        Some(v)
    }

    #[inline]
    unsafe fn insert_fixup(&mut self, mut node: NodePtr<K, V>) {
        let mut parent;
        let mut gparent;

        while node.parent().is_red_color() {
            parent = node.parent();
            gparent = parent.parent();
            //若“父节点”是“祖父节点的左孩子”
            if parent == gparent.left() {
                // Case 1条件：叔叔节点是红色
                let mut uncle = gparent.right();
                if !uncle.is_null() && uncle.is_red_color() {
                    uncle.set_black_color();
                    parent.set_black_color();
                    gparent.set_red_color();
                    node = gparent;
                    continue;
                }

                // Case 2条件：叔叔是黑色，且当前节点是右孩子
                if parent.right() == node {
                    self.left_rotate(parent);
                    let temp = parent;
                    parent = node;
                    node = temp;
                }

                // Case 3条件：叔叔是黑色，且当前节点是左孩子。
                parent.set_black_color();
                gparent.set_red_color();
                self.right_rotate(gparent);
            } else {
                // Case 1条件：叔叔节点是红色
                let mut uncle = gparent.left();
                if !uncle.is_null() && uncle.is_red_color() {
                    uncle.set_black_color();
                    parent.set_black_color();
                    gparent.set_red_color();
                    node = gparent;
                    continue;
                }

                // Case 2条件：叔叔是黑色，且当前节点是右孩子
                if parent.left() == node {
                    self.right_rotate(parent);
                    let temp = parent;
                    parent = node;
                    node = temp;
                }

                // Case 3条件：叔叔是黑色，且当前节点是左孩子。
                parent.set_black_color();
                gparent.set_red_color();
                self.left_rotate(gparent);
            }
        }
        self.root.set_black_color();
    }

    #[inline]
    pub fn insert(&mut self, k: K, v: V) {
        let mut node = NodePtr::new(k, v);
        let mut y = NodePtr::null();
        let mut x = self.root;

        while !x.is_null() {
            y = x;
            unsafe { (*y.0).size += 1 };
            match node.cmp(&&mut x) {
                Ordering::Less => {
                    x = x.left();
                }
                _ => {
                    x = x.right();
                }
            };
        }
        node.set_parent(y);

        if y.is_null() {
            self.root = node;
        } else {
            match node.cmp(&&mut y) {
                Ordering::Less => {
                    y.set_left(node);
                }
                _ => {
                    y.set_right(node);
                }
            };
        }

        node.set_red_color();

        let mut pnode = y;
        while !pnode.is_null() {
            pnode.refresh_size();
            pnode = pnode.parent();
        }

        unsafe {
            self.insert_fixup(node);
        }
    }

    #[inline]
    fn find_node(&self, k: &K) -> NodePtr<K, V> {
        if self.root.is_null() {
            return NodePtr::null();
        }
        let mut temp = &self.root;
        unsafe {
            loop {
                let next = match k.cmp(&(*temp.0).key) {
                    Ordering::Less => &mut (*temp.0).left,
                    Ordering::Greater => &mut (*temp.0).right,
                    Ordering::Equal => return *temp,
                };
                if next.is_null() {
                    break;
                }
                temp = next;
            }
        }
        NodePtr::null()
    }

    #[inline]
    fn first_child(&self) -> NodePtr<K, V> {
        if self.root.is_null() {
            NodePtr::null()
        } else {
            let mut temp = self.root;
            while !temp.left().is_null() {
                temp = temp.left();
            }
            return temp;
        }
    }

    #[inline]
    fn last_child(&self) -> NodePtr<K, V> {
        if self.root.is_null() {
            NodePtr::null()
        } else {
            let mut temp = self.root;
            while !temp.right().is_null() {
                temp = temp.right();
            }
            return temp;
        }
    }

    #[inline]
    pub fn get_first(&self) -> Option<(&K, &V)> {
        let first = self.first_child();
        if first.is_null() {
            return None;
        }
        unsafe { Some((&(*first.0).key, &(*first.0).value)) }
    }

    #[inline]
    pub fn get_last(&self) -> Option<(&K, &V)> {
        let last = self.last_child();
        if last.is_null() {
            return None;
        }
        unsafe { Some((&(*last.0).key, &(*last.0).value)) }
    }

    #[inline]
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        let first = self.first_child();
        if first.is_null() {
            return None;
        }
        unsafe { Some(self.delete(first)) }
    }

    #[inline]
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        let last = self.last_child();
        if last.is_null() {
            return None;
        }
        unsafe { Some(self.delete(last)) }
    }

    #[inline]
    pub fn get_first_mut(&mut self) -> Option<(&K, &mut V)> {
        let first = self.first_child();
        if first.is_null() {
            return None;
        }
        unsafe { Some((&(*first.0).key, &mut (*first.0).value)) }
    }

    #[inline]
    pub fn get_last_mut(&mut self) -> Option<(&K, &mut V)> {
        let last = self.last_child();
        if last.is_null() {
            return None;
        }
        unsafe { Some((&(*last.0).key, &mut (*last.0).value)) }
    }

    #[inline]
    pub fn get(&self, k: &K) -> Option<&V> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }

        unsafe { Some(&(*node.0).value) }
    }

    #[inline]
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }

        unsafe { Some(&mut (*node.0).value) }
    }

    #[inline]
    pub fn contains_key(&self, k: &K) -> bool {
        let node = self.find_node(k);
        if node.is_null() {
            return false;
        }
        true
    }

    #[inline]
    fn clear_recurse(&mut self, current: NodePtr<K, V>) {
        if !current.is_null() {
            unsafe {
                self.clear_recurse(current.left());
                self.clear_recurse(current.right());
                Box::from_raw(current.0);
            }
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        let root = self.root;
        self.root = NodePtr::null();
        self.clear_recurse(root);
    }

    /// Empties the `OSTree` without freeing objects in it.
    #[inline]
    fn fast_clear(&mut self) {
        self.root = NodePtr::null();
    }

    #[inline]
    pub fn remove(&mut self, k: &K) -> Option<V> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }
        unsafe { Some(self.delete(node).1) }
    }

    #[inline]
    unsafe fn delete_fixup(&mut self, mut node: NodePtr<K, V>, mut parent: NodePtr<K, V>) {
        let mut other;
        while node != self.root && node.is_black_color() {
            if parent.left() == node {
                other = parent.right();
                //x的兄弟w是红色的
                if other.is_red_color() {
                    other.set_black_color();
                    parent.set_red_color();
                    self.left_rotate(parent);
                    other = parent.right();
                }

                //x的兄弟w是黑色，且w的俩个孩子也都是黑色的
                if other.left().is_black_color() && other.right().is_black_color() {
                    other.set_red_color();
                    node = parent;
                    parent = node.parent();
                } else {
                    //x的兄弟w是黑色的，并且w的左孩子是红色，右孩子为黑色。
                    if other.right().is_black_color() {
                        other.left().set_black_color();
                        other.set_red_color();
                        self.right_rotate(other);
                        other = parent.right();
                    }
                    //x的兄弟w是黑色的；并且w的右孩子是红色的，左孩子任意颜色。
                    other.set_color(parent.get_color());
                    parent.set_black_color();
                    other.right().set_black_color();
                    self.left_rotate(parent);
                    node = self.root;
                    break;
                }
            } else {
                other = parent.left();
                //x的兄弟w是红色的
                if other.is_red_color() {
                    other.set_black_color();
                    parent.set_red_color();
                    self.right_rotate(parent);
                    other = parent.left();
                }

                //x的兄弟w是黑色，且w的俩个孩子也都是黑色的
                if other.left().is_black_color() && other.right().is_black_color() {
                    other.set_red_color();
                    node = parent;
                    parent = node.parent();
                } else {
                    //x的兄弟w是黑色的，并且w的左孩子是红色，右孩子为黑色。
                    if other.left().is_black_color() {
                        other.right().set_black_color();
                        other.set_red_color();
                        self.left_rotate(other);
                        other = parent.left();
                    }
                    //x的兄弟w是黑色的；并且w的右孩子是红色的，左孩子任意颜色。
                    other.set_color(parent.get_color());
                    parent.set_black_color();
                    other.left().set_black_color();
                    self.right_rotate(parent);
                    node = self.root;
                    break;
                }
            }
        }

        node.set_black_color();
    }

    #[inline]
    unsafe fn delete(&mut self, node: NodePtr<K, V>) -> (K, V) {
        let mut child;
        let mut parent;
        let color;

        // 被删除节点的"左右孩子都不为空"的情况。
        if !node.left().is_null() && !node.right().is_null() {
            // 被删节点的后继节点。(称为"取代节点")
            // 用它来取代"被删节点"的位置，然后再将"被删节点"去掉。
            let mut replace = node.right().min_node();
            if node == self.root {
                self.root = replace;
            } else {
                if node.parent().left() == node {
                    node.parent().set_left(replace);
                } else {
                    node.parent().set_right(replace);
                }
            }

            // child是"取代节点"的右孩子，也是需要"调整的节点"。
            // "取代节点"肯定不存在左孩子！因为它是一个后继节点。
            child = replace.right();
            parent = replace.parent();
            color = replace.get_color();
            if parent == node {
                parent = replace;
            } else {
                if !child.is_null() {
                    child.set_parent(parent);
                }
                parent.set_left(child);
                replace.set_right(node.right());
                node.right().set_parent(replace);
            }

            replace.set_parent(node.parent());
            replace.set_color(node.get_color());
            replace.set_left(node.left());
            node.left().set_parent(replace);

            let mut pnode = parent;
            while !pnode.is_null() {
                pnode.refresh_size();
                pnode = pnode.parent();
            }

            if color == Color::Black {
                self.delete_fixup(child, parent);
            }

            let obj = Box::from_raw(node.0);
            return obj.pair();
        }

        if !node.left().is_null() {
            child = node.left();
        } else {
            child = node.right();
        }

        parent = node.parent();
        color = node.get_color();
        if !child.is_null() {
            child.set_parent(parent);
        }

        if self.root == node {
            self.root = child
        } else {
            if parent.left() == node {
                parent.set_left(child);
            } else {
                parent.set_right(child);
            }
        }

        let mut pnode = parent;
        while !pnode.is_null() {
            pnode.refresh_size();
            pnode = pnode.parent();
        }

        if color == Color::Black {
            self.delete_fixup(child, parent);
        }

        let obj = Box::from_raw(node.0);
        return obj.pair();
    }

    /// Return the keys iter
    #[inline]
    pub fn keys(&self) -> Keys<K, V> {
        Keys { inner: self.iter() }
    }

    /// Return the value iter
    #[inline]
    pub fn values(&self) -> Values<K, V> {
        Values { inner: self.iter() }
    }

    /// Return the value iter mut
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// Return the key and value iter
    #[inline]
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            head: self.first_child(),
            tail: self.last_child(),
            len: self.len(),
            _marker: marker::PhantomData,
        }
    }

    /// Return the key and mut value iter
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            head: self.first_child(),
            tail: self.last_child(),
            len: self.len(),
            _marker: marker::PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::OSTree;

    #[test]
    fn test_insert() {
        let mut m = OSTree::new();
        assert_eq!(m.len(), 0);
        m.insert(1, 2);
        assert_eq!(m.len(), 1);
        m.insert(2, 4);
        assert_eq!(m.len(), 2);
        m.insert(2, 6);
        assert_eq!(m.len(), 3);
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&2).unwrap(), 4);
        assert_eq!(*m.get(&2).unwrap(), 4);
    }

    #[test]
    fn test_replace() {
        let mut m = OSTree::new();
        assert_eq!(m.len(), 0);
        m.insert(2, 4);
        assert_eq!(m.len(), 1);
        assert_eq!(m.replace_or_insert(2, 6).unwrap(), 4);
        assert_eq!(m.len(), 1);
        assert_eq!(*m.get(&2).unwrap(), 6);
    }

    #[test]
    fn test_clone() {
        let mut m = OSTree::new();
        assert_eq!(m.len(), 0);
        m.insert(1, 2);
        assert_eq!(m.len(), 1);
        m.insert(2, 4);
        assert_eq!(m.len(), 2);
        let m2 = m.clone();
        m.clear();
        assert_eq!(*m2.get(&1).unwrap(), 2);
        assert_eq!(*m2.get(&2).unwrap(), 4);
        m2.print_tree();
        assert_eq!(m2.len(), 2);
    }

    #[test]
    fn test_empty_remove() {
        let mut m: OSTree<isize, bool> = OSTree::new();
        assert_eq!(m.remove(&0), None);
    }

    #[test]
    fn test_empty_iter() {
        let mut m: OSTree<isize, bool> = OSTree::new();
        assert_eq!(m.iter().next(), None);
        assert_eq!(m.iter_mut().next(), None);
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());
        assert_eq!(m.into_iter().next(), None);
    }

    #[test]
    fn test_lots_of_insertions() {
        let mut m = OSTree::new();

        // Try this a few times to make sure we never screw up the hashmap's
        // internal state.
        for _ in 0..10 {
            assert!(m.is_empty());

            for i in 1..101 {
                m.insert(i, i);

                for j in 1..i + 1 {
                    let r = m.get(&j);
                    assert_eq!(r, Some(&j));
                }

                for j in i + 1..101 {
                    let r = m.get(&j);
                    assert_eq!(r, None);
                }
            }

            for i in 101..201 {
                assert!(!m.contains_key(&i));
            }

            // remove forwards
            for i in 1..101 {
                assert!(m.remove(&i).is_some());

                for j in 1..i + 1 {
                    assert!(!m.contains_key(&j));
                }

                for j in i + 1..101 {
                    assert!(m.contains_key(&j));
                }
            }

            for i in 1..101 {
                assert!(!m.contains_key(&i));
            }

            for i in 1..101 {
                m.insert(i, i);
            }

            // remove backwards
            for i in (1..101).rev() {
                assert!(m.remove(&i).is_some());

                for j in i..101 {
                    assert!(!m.contains_key(&j));
                }

                for j in 1..i {
                    assert!(m.contains_key(&j));
                }
            }
        }
    }

    #[test]
    fn test_find_mut() {
        let mut m = OSTree::new();
        m.insert(1, 12);
        m.insert(2, 8);
        m.insert(5, 14);
        let new = 100;
        match m.get_mut(&5) {
            None => panic!(),
            Some(x) => *x = new,
        }
        assert_eq!(m.get(&5), Some(&new));
    }

    #[test]
    fn test_remove() {
        let mut m = OSTree::new();
        m.insert(1, 2);
        assert_eq!(*m.get(&1).unwrap(), 2);
        m.insert(5, 3);
        assert_eq!(*m.get(&5).unwrap(), 3);
        m.insert(9, 4);
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&5).unwrap(), 3);
        assert_eq!(*m.get(&9).unwrap(), 4);
        assert_eq!(m.remove(&1).unwrap(), 2);
        assert_eq!(m.remove(&5).unwrap(), 3);
        assert_eq!(m.remove(&9).unwrap(), 4);
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn test_is_empty() {
        let mut m = OSTree::new();
        m.insert(1, 2);
        assert!(!m.is_empty());
        assert!(m.remove(&1).is_some());
        assert!(m.is_empty());
    }

    #[test]
    fn test_pop() {
        let mut m = OSTree::new();
        m.insert(2, 4);
        m.insert(1, 2);
        m.insert(3, 6);
        assert_eq!(m.len(), 3);
        assert_eq!(m.pop_first(), Some((1, 2)));
        assert_eq!(m.len(), 2);
        assert_eq!(m.pop_last(), Some((3, 6)));
        assert_eq!(m.len(), 1);
        assert_eq!(m.get_first(), Some((&2, &4)));
        assert_eq!(m.get_last(), Some((&2, &4)));
    }

    #[test]
    fn test_iterate() {
        let mut m = OSTree::new();
        for i in 0..32 {
            m.insert(i, i * 2);
        }
        assert_eq!(m.len(), 32);

        let mut observed: u32 = 0;

        for (k, v) in m.iter() {
            assert_eq!(*v, *k * 2);
            observed |= 1 << *k;
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

    #[test]
    fn test_keys() {
        let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
        let map: OSTree<_, _> = vec.into_iter().collect();
        let keys: Vec<_> = map.keys().cloned().collect();
        assert_eq!(keys.len(), 3);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
        assert!(keys.contains(&3));
    }

    #[test]
    fn test_values() {
        let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
        let map: OSTree<_, _> = vec.into_iter().collect();
        let values: Vec<_> = map.values().cloned().collect();
        assert_eq!(values.len(), 3);
        assert!(values.contains(&'a'));
        assert!(values.contains(&'b'));
        assert!(values.contains(&'c'));
    }

    #[test]
    fn test_values_mut() {
        let vec = vec![(1, 1), (2, 2), (3, 3)];
        let mut map: OSTree<_, _> = vec.into_iter().collect();
        for value in map.values_mut() {
            *value = (*value) * 2
        }
        let values: Vec<_> = map.values().cloned().collect();
        assert_eq!(values.len(), 3);
        assert!(values.contains(&2));
        assert!(values.contains(&4));
        assert!(values.contains(&6));
    }

    #[test]
    fn test_find() {
        let mut m = OSTree::new();
        assert!(m.get(&1).is_none());
        m.insert(1, 2);
        match m.get(&1) {
            None => panic!(),
            Some(v) => assert_eq!(*v, 2),
        }
    }

    #[test]
    fn test_eq() {
        let mut m1 = OSTree::new();
        m1.insert(1, 2);
        m1.insert(2, 3);
        m1.insert(3, 4);

        let mut m2 = OSTree::new();
        m2.insert(1, 2);
        m2.insert(2, 3);

        assert!(m1 != m2);

        m2.insert(3, 4);

        assert_eq!(m1, m2);
    }

    #[test]
    fn test_show() {
        let mut map = OSTree::new();
        let empty: OSTree<i32, i32> = OSTree::new();

        map.insert(1, 2);
        map.insert(3, 4);

        let map_str = format!("{:?}", map);

        assert!(map_str == "{1: 2, 3: 4}" || map_str == "{3: 4, 1: 2}");
        assert_eq!(format!("{:?}", empty), "{}");
    }

    #[test]
    fn test_from_iter() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: OSTree<_, _> = xs.iter().cloned().collect();

        for &(k, v) in &xs {
            assert_eq!(map.get(&k), Some(&v));
        }
    }

    #[test]
    fn test_size_hint() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: OSTree<_, _> = xs.iter().cloned().collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_iter_len() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: OSTree<_, _> = xs.iter().cloned().collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.count(), 3);
    }

    #[test]
    fn test_mut_size_hint() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let mut map: OSTree<_, _> = xs.iter().cloned().collect();

        let mut iter = map.iter_mut();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_iter_mut_len() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let mut map: OSTree<_, _> = xs.iter().cloned().collect();

        let mut iter = map.iter_mut();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.count(), 3);
    }

    #[test]
    fn test_index() {
        let mut map = OSTree::new();

        map.insert(1, 2);
        map.insert(2, 1);
        map.insert(3, 4);

        assert_eq!(map[&2], 1);
    }

    #[test]
    #[should_panic]
    fn test_index_nonexistent() {
        let mut map = OSTree::new();

        map.insert(1, 2);
        map.insert(2, 1);
        map.insert(3, 4);

        map[&4];
    }

    #[test]
    fn test_extend_iter() {
        let mut a = OSTree::new();
        a.insert(1, "one");
        let mut b = OSTree::new();
        b.insert(2, "two");
        b.insert(3, "three");

        a.extend(b.into_iter());

        assert_eq!(a.len(), 3);
        assert_eq!(a[&1], "one");
        assert_eq!(a[&2], "two");
        assert_eq!(a[&3], "three");
    }

    #[test]
    fn test_rank() {
        let mut a = OSTree::new();
        a.insert(1, ());
        a.insert(2, ());
        a.insert(4, ());
        a.insert(3, ());
        a.insert(11, ());
        a.insert(9, ());
        a.insert(7, ());
        a.remove(&2);
        a.remove(&11);

        assert_eq!(a.rank(&99), None);
        assert_eq!(a.rank(&9).unwrap(), 4);
        assert_eq!(a.rank(&7).unwrap(), 3);
        assert_eq!(a.rank(&4).unwrap(), 2);
        assert_eq!(a.rank(&3).unwrap(), 1);
        assert_eq!(a.rank(&1).unwrap(), 0);
    }
    // 1,3,4,7,9

    #[test]
    fn test_select() {
        let mut a = OSTree::new();
        a.insert(1, ());
        a.insert(2, ());
        a.insert(4, ());
        a.insert(3, ());
        a.insert(11, ());
        a.insert(9, ());
        a.insert(7, ());
        a.remove(&2);
        a.remove(&11);

        a.print_tree();
        assert_eq!(a.select(99), None);
        assert_eq!(a.select(4).unwrap().0, &9);
        assert_eq!(a.select(3).unwrap().0, &7);
        assert_eq!(a.select(2).unwrap().0, &4);
        assert_eq!(a.select(1).unwrap().0, &3);
        assert_eq!(a.select(0).unwrap().0, &1);
    }
}
