use std::cmp::Ord;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::ptr::NonNull;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum Color {
    Red,
    Black,
}

/*****************OSTreeNode***************************/
pub(crate) struct OSTreeNode<K: Ord> {
    pub(crate) color: Color,
    pub(crate) left: NodePtr<K>,
    pub(crate) right: NodePtr<K>,
    pub(crate) parent: NodePtr<K>,
    pub(crate) key: K,
    pub(crate) count: usize,
    pub(crate) size: usize, // self.size = self.left.size + self.right.size + self.count
}

impl<K: Ord> OSTreeNode<K> {
    #[inline]
    pub(crate) fn pair(self) -> (K, usize) {
        (self.key, self.count)
    }
}

impl<K> Debug for OSTreeNode<K>
where
    K: Ord + Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "k:{:?} n:{} c:{:?}", self.key, self.count, self.color)
    }
}

/*****************NodePtr***************************/
#[derive(Debug)]
pub(crate) struct NodePtr<K: Ord>(pub(crate) Option<NonNull<OSTreeNode<K>>>);

impl<K: Ord> Clone for NodePtr<K> {
    fn clone(&self) -> NodePtr<K> {
        NodePtr(self.0)
    }
}

impl<K: Ord> Copy for NodePtr<K> {}

impl<K: Ord> Ord for NodePtr<K> {
    fn cmp(&self, other: &NodePtr<K>) -> Ordering {
        unsafe { self.as_ptr().as_ref().key.cmp(&other.as_ptr().as_ref().key) }
    }
}

impl<K: Ord> PartialOrd for NodePtr<K> {
    fn partial_cmp(&self, other: &NodePtr<K>) -> Option<Ordering> {
        unsafe { Some(self.as_ptr().as_ref().key.cmp(&other.as_ptr().as_ref().key)) }
    }
}

impl<K: Ord> PartialEq for NodePtr<K> {
    fn eq(&self, other: &NodePtr<K>) -> bool {
        self.0 == other.0
    }
}

impl<K: Ord> Eq for NodePtr<K> {}

impl<K: Ord> NodePtr<K> {
    pub(crate) fn with_count(k: K, count: usize) -> NodePtr<K> {
        let node = OSTreeNode {
            color: Color::Black,
            left: NodePtr::null(),
            right: NodePtr::null(),
            parent: NodePtr::null(),
            key: k,
            count,
            size: count,
        };
        NodePtr(Some(unsafe {
            NonNull::new_unchecked(Box::into_raw(Box::new(node)))
        }))
    }

    #[inline]
    pub(crate) fn set_color(&mut self, color: Color) {
        match self.0 {
            Some(mut ptr) => unsafe { ptr.as_mut().color = color },
            None => {}
        }
    }

    #[inline]
    pub(crate) fn set_red_color(&mut self) {
        self.set_color(Color::Red);
    }

    #[inline]
    pub(crate) fn set_black_color(&mut self) {
        self.set_color(Color::Black);
    }

    #[inline]
    pub(crate) fn get_color(&self) -> Color {
        match self.0 {
            Some(ptr) => unsafe { ptr.as_ref().color },
            None => Color::Black,
        }
    }

    #[inline]
    pub(crate) fn is_red_color(&self) -> bool {
        if self.is_null() {
            return false;
        }
        self.get_color() == Color::Red
    }

    #[inline]
    pub(crate) fn is_black_color(&self) -> bool {
        if self.is_null() {
            return true;
        }
        self.get_color() == Color::Black
    }

    #[inline]
    pub(crate) fn is_left_child(&self) -> bool {
        self.parent().left() == *self
    }

    #[inline]
    pub(crate) fn is_right_child(&self) -> bool {
        self.parent().right() == *self
    }

    #[inline]
    pub(crate) fn min_node(self) -> NodePtr<K> {
        let mut temp = self.clone();
        while !temp.left().is_null() {
            temp = temp.left();
        }
        return temp;
    }

    #[inline]
    pub(crate) fn max_node(self) -> NodePtr<K> {
        let mut temp = self.clone();
        while !temp.right().is_null() {
            temp = temp.right();
        }
        return temp;
    }

    #[inline]
    pub(crate) fn next(self) -> NodePtr<K> {
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
    pub(crate) fn prev(self) -> NodePtr<K> {
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
    pub(crate) fn set_parent(&mut self, parent: NodePtr<K>) {
        match self.0 {
            Some(mut ptr) => unsafe { ptr.as_mut().parent = parent },
            None => {}
        }
    }

    #[inline]
    pub(crate) fn set_left(&mut self, left: NodePtr<K>) {
        match self.0 {
            Some(mut ptr) => unsafe { ptr.as_mut().left = left },
            None => {}
        }
    }

    #[inline]
    pub(crate) fn set_right(&mut self, right: NodePtr<K>) {
        match self.0 {
            Some(mut ptr) => unsafe { ptr.as_mut().right = right },
            None => {}
        }
    }

    #[inline]
    pub(crate) fn parent(&self) -> NodePtr<K> {
        match self.0 {
            Some(ptr) => unsafe { ptr.as_ref().parent },
            None => NodePtr::null(),
        }
    }

    #[inline]
    pub(crate) fn left(&self) -> NodePtr<K> {
        if self.is_null() {
            return NodePtr::null();
        }
        let ptr = self.0.unwrap();
        unsafe { ptr.as_ref().left.clone() }
    }

    #[inline]
    pub(crate) fn right(&self) -> NodePtr<K> {
        if self.is_null() {
            return NodePtr::null();
        }
        let ptr = self.0.unwrap();
        unsafe { ptr.as_ref().right.clone() }
    }

    #[inline]
    pub(crate) fn null() -> NodePtr<K> {
        NodePtr(None)
    }

    #[inline]
    pub(crate) fn is_null(&self) -> bool {
        self.0.is_none()
    }

    #[inline]
    pub(crate) fn into_box(self) -> Box<OSTreeNode<K>> {
        let ptr = self.0.unwrap();
        unsafe { Box::from_raw(ptr.as_ptr()) }
    }

    #[inline]
    pub(crate) fn as_ptr(&self) -> NonNull<OSTreeNode<K>> {
        self.0.expect("Null Node")
    }

    #[inline]
    pub(crate) fn key(&self) -> K
    where
        K: Clone,
    {
        unsafe { self.0.expect("Null Node").as_ref().key.clone() }
    }

    #[inline]
    pub(crate) fn count(&self) -> usize {
        match self.0 {
            Some(ptr) => unsafe { ptr.as_ref().count },
            None => 0,
        }
    }

    #[inline]
    pub(crate) fn set_count(&self, count: usize) {
        match self.0 {
            Some(mut ptr) => unsafe { ptr.as_mut().count = count },
            None => {}
        }
    }

    #[inline]
    pub(crate) fn size(&self) -> usize {
        match self.0 {
            Some(ptr) => unsafe { ptr.as_ref().size },
            None => 0,
        }
    }

    #[inline]
    pub(crate) fn set_size(&self, size: usize) {
        match self.0 {
            Some(mut ptr) => unsafe { ptr.as_mut().size = size },
            None => {}
        }
    }

    #[inline]
    pub(crate) fn refresh_size(&self) {
        if self.is_null() {
            return;
        } else {
            self.set_size(self.count() + self.left().size() + self.right().size())
        }
    }

    // refresh size until root
    #[inline]
    pub(crate) fn propagate_size(&self) {
        let mut node = *self;
        while !node.is_null() {
            node.refresh_size();
            node = node.parent();
        }
    }

    pub(crate) fn select(&self, i: usize) -> Option<NodePtr<K>> {
        // Returns the i'th element (zero-indexed) of the elements in t

        if i >= self.size() {
            return None;
        }

        let l = self.left().size();
        if l <= i && i < l + self.count() {
            Some(*self)
        } else if i < l {
            self.left().select(i)
        } else {
            self.right().select(i - l - self.count())
        }
    }
}

impl<K: Ord + Clone> NodePtr<K> {
    pub unsafe fn deep_clone(&self) -> NodePtr<K> {
        let mut node = NodePtr::with_count(self.as_ptr().as_ref().key.clone(), self.count());
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
