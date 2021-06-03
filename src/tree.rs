use crate::iters::{Counts, IntoIter, Iter, Keys};
use crate::node::Color;
use crate::node::NodePtr;
use std::cmp::Ord;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::iter::{FromIterator, IntoIterator};

pub struct OSTree<K: Ord> {
    root: NodePtr<K>,
}

unsafe impl<K: Ord> Send for OSTree<K> {}

// Drop all owned pointers if the tree is dropped
impl<K: Ord> Drop for OSTree<K> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

/// If key and value are both impl Clone, we can call clone to get a copy.
impl<K: Ord + Clone> Clone for OSTree<K> {
    fn clone(&self) -> OSTree<K> {
        unsafe {
            let mut new = OSTree::new();
            new.root = self.root.deep_clone();
            new
        }
    }
}

impl<K> Debug for OSTree<K>
where
    K: Ord + Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Ord> OSTree<K> {
    fn size(&self) -> usize {
        self.root.size()
    }

    /// Get the (key, count) of the given rank, 0 based
    /// Return None if the rank is out of range
    ///
    /// # Examples
    /// ```rust
    /// use order_stats_tree::OSTree;
    /// let mut m = OSTree::new();
    ///
    /// m.increase(1, 2);
    /// m.increase(2, 3);
    /// assert_eq!(m.select(0).unwrap(), (&1, 2));
    /// ```
    pub fn select(&self, i: usize) -> Option<(&K, usize)> {
        match self.root.select(i) {
            Some(node) => unsafe { Some((&(*node.0).key, node.count())) },
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
    /// m.increase(1, 2);
    /// m.increase(2, 4);
    /// assert_eq!(m.rank(&2).unwrap(), 2);
    /// ```
    pub fn rank(&self, x: &K) -> Option<usize> {
        // Returns the position of x (one-indexed) in the linear sorted list of elements of the tree T
        let x = self.find_node(x);
        if x.is_null() {
            return None;
        }

        let mut rank = x.left().size();
        let mut y = x;
        while y != self.root {
            if y == y.parent().right() {
                rank = rank + y.parent().left().size() + y.parent().count();
            }
            y = y.parent();
        }
        Some(rank)
    }
}

/// This is a method to help us to get inner struct.
impl<K: Ord + Debug> OSTree<K> {
    fn tree_print(&self, node: NodePtr<K>, direction: i32) {
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
impl<K> PartialEq for OSTree<K>
where
    K: Eq + Ord,
{
    fn eq(&self, other: &OSTree<K>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, count)| other.get_count(key).map_or(false, |c| count == c))
    }
}

impl<K> Eq for OSTree<K> where K: Eq + Ord {}

impl<K: Ord> FromIterator<(K, usize)> for OSTree<K> {
    fn from_iter<T: IntoIterator<Item = (K, usize)>>(iter: T) -> OSTree<K> {
        let mut tree = OSTree::new();
        tree.extend(iter);
        tree
    }
}

impl<K: Ord> FromIterator<K> for OSTree<K> {
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> OSTree<K> {
        let mut tree = OSTree::new();
        tree.extend(iter);
        tree
    }
}

/// OSTree into iter
impl<K: Ord> Extend<(K, usize)> for OSTree<K> {
    fn extend<T: IntoIterator<Item = (K, usize)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        for (k, v) in iter {
            self.increase(k, v);
        }
    }
}

/// OSTree into iter
impl<K: Ord> Extend<K> for OSTree<K> {
    fn extend<T: IntoIterator<Item = K>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        for k in iter {
            self.increase(k, 1);
        }
    }
}

impl<K: Ord> IntoIterator for OSTree<K> {
    type Item = (K, usize);
    type IntoIter = IntoIter<K>;

    #[inline]
    fn into_iter(mut self) -> IntoIter<K> {
        let iter = if self.root.is_null() {
            IntoIter::new(NodePtr::null(), NodePtr::null(), self.len())
        } else {
            IntoIter::new(self.first_child(), self.last_child(), self.len())
        };
        self.fast_clear();
        iter
    }
}

impl<K: Ord> OSTree<K> {
    /// Creates an empty `OSTree`.
    pub fn new() -> OSTree<K> {
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
    unsafe fn left_rotate(&mut self, mut x: NodePtr<K>) {
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
    unsafe fn right_rotate(&mut self, mut y: NodePtr<K>) {
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

    #[inline]
    unsafe fn insert_fixup(&mut self, mut node: NodePtr<K>) {
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
    pub fn increase(&mut self, k: K, count: usize) {
        let mut node = NodePtr::with_count(k, count);
        let mut y = NodePtr::null();
        let mut x = self.root;

        while !x.is_null() {
            y = x;

            match node.cmp(&&mut x) {
                Ordering::Less => {
                    x = x.left();
                }
                Ordering::Greater => {
                    x = x.right();
                }
                Ordering::Equal => {
                    x.set_count(x.count() + count);
                    x.propagate_size();
                    return;
                }
            };
        }

        // the node is not found

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

        y.propagate_size();

        unsafe {
            self.insert_fixup(node);
        }
    }

    #[inline]
    fn find_node(&self, k: &K) -> NodePtr<K> {
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
    fn first_child(&self) -> NodePtr<K> {
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
    fn last_child(&self) -> NodePtr<K> {
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
    pub fn get_first(&self) -> Option<(&K, usize)> {
        let first = self.first_child();
        if first.is_null() {
            return None;
        }
        unsafe { Some((&(*first.0).key, first.count())) }
    }

    #[inline]
    pub fn get_last(&self) -> Option<(&K, usize)> {
        let last = self.last_child();
        if last.is_null() {
            return None;
        }
        unsafe { Some((&(*last.0).key, last.count())) }
    }

    #[inline]
    pub fn pop_first(&mut self) -> Option<(K, usize)> {
        let first = self.first_child();
        if first.is_null() {
            return None;
        }
        unsafe { Some(self.delete(first)) }
    }

    #[inline]
    pub fn pop_last(&mut self) -> Option<(K, usize)> {
        let last = self.last_child();
        if last.is_null() {
            return None;
        }
        unsafe { Some(self.delete(last)) }
    }

    #[inline]
    pub fn get_count(&self, k: &K) -> Option<usize> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }

        Some(node.count())
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
    fn clear_recurse(&mut self, current: NodePtr<K>) {
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
    pub fn remove(&mut self, k: &K) -> Option<usize> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }
        let count = node.count();
        unsafe { self.delete(node) };
        Some(count)
    }

    #[inline]
    pub fn decrease(&mut self, k: &K, count: usize) -> Option<usize> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }
        unsafe { self.decrease_impl(node, count) }
    }

    // the nodeptr should not be null
    #[inline]
    unsafe fn decrease_impl(&mut self, node: NodePtr<K>, count: usize) -> Option<usize> {
        if node.count() <= count {
            self.delete(node);
            Some(0)
        } else {
            node.set_count(node.count() - count);
            node.propagate_size();
            Some(node.count())
        }
    }

    #[inline]
    unsafe fn delete_fixup(&mut self, mut node: NodePtr<K>, mut parent: NodePtr<K>) {
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
    unsafe fn delete(&mut self, node: NodePtr<K>) -> (K, usize) {
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
    pub fn keys(&self) -> Keys<K> {
        Keys::new(self.iter())
    }

    /// Return the counts iter
    #[inline]
    pub fn counts(&mut self) -> Counts<K> {
        Counts::new(self.iter())
    }

    /// Return the key and value iter
    #[inline]
    pub fn iter(&self) -> Iter<K> {
        Iter::new(self.first_child(), self.last_child(), self.len())
    }
}
