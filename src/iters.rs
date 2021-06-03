use crate::node::NodePtr;
use std::fmt;
use std::fmt::Debug;
use std::marker;

pub struct Keys<'a, K: Ord + 'a> {
    inner: Iter<'a, K>,
}

impl<'a, K: Ord + 'a> Keys<'a, K> {
    pub(crate) fn new(inner: Iter<'a, K>) -> Self {
        Self { inner }
    }
}

impl<'a, K: Ord> Clone for Keys<'a, K> {
    fn clone(&self) -> Keys<'a, K> {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K: Ord + Debug> fmt::Debug for Keys<'a, K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord> Iterator for Keys<'a, K> {
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

pub struct Counts<'a, K: 'a + Ord> {
    inner: Iter<'a, K>,
}

impl<'a, K: Ord> Counts<'a, K> {
    pub(crate) fn new(inner: Iter<'a, K>) -> Self {
        Self { inner }
    }
}
impl<'a, K: Ord> Clone for Counts<'a, K> {
    fn clone(&self) -> Counts<'a, K> {
        Counts {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K: Ord + Debug> fmt::Debug for Counts<'a, K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord> Iterator for Counts<'a, K> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// Convert OSTree to iter, move out the tree.
pub struct IntoIter<K: Ord> {
    head: NodePtr<K>,
    tail: NodePtr<K>,
    len: usize,
}

impl<K: Ord> IntoIter<K> {
    pub(crate) fn new(head: NodePtr<K>, tail: NodePtr<K>, len: usize) -> Self {
        IntoIter { head, tail, len }
    }
}

// Drop all owned pointers if the collection is dropped
impl<K: Ord> Drop for IntoIter<K> {
    #[inline]
    fn drop(&mut self) {
        for (_, _) in self {}
    }
}

impl<K: Ord> Iterator for IntoIter<K> {
    type Item = (K, usize);

    fn next(&mut self) -> Option<(K, usize)> {
        if self.len == 0 {
            return None;
        }

        if self.head.is_null() {
            return None;
        }

        let next = self.head.next();
        let obj = unsafe { Box::from_raw(self.head.0) };
        let (k, c) = obj.pair();
        self.head = next;
        self.len -= 1;
        Some((k, c))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K: Ord> DoubleEndedIterator for IntoIter<K> {
    #[inline]
    fn next_back(&mut self) -> Option<(K, usize)> {
        if self.len == 0 {
            return None;
        }

        if self.tail.is_null() {
            return None;
        }

        let prev = self.tail.prev();
        let obj = unsafe { Box::from_raw(self.tail.0) };
        let (k, c) = obj.pair();
        self.tail = prev;
        self.len -= 1;
        Some((k, c))
    }
}

pub struct Iter<'a, K: Ord + 'a> {
    head: NodePtr<K>,
    tail: NodePtr<K>,
    len: usize,
    _marker: marker::PhantomData<&'a ()>,
}

impl<'a, K: Ord> Iter<'a, K> {
    pub(crate) fn new(head: NodePtr<K>, tail: NodePtr<K>, len: usize) -> Self {
        Iter {
            head,
            tail,
            len,
            _marker: marker::PhantomData,
        }
    }
}

impl<'a, K: Ord + 'a> Clone for Iter<'a, K> {
    fn clone(&self) -> Iter<'a, K> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: self._marker,
        }
    }
}

impl<'a, K: Ord + 'a> Iterator for Iter<'a, K> {
    type Item = (&'a K, usize);

    fn next(&mut self) -> Option<(&'a K, usize)> {
        if self.len == 0 {
            return None;
        }

        if self.head.is_null() {
            return None;
        }

        let (k, v) = unsafe { (&(*self.head.0).key, self.head.count()) };
        self.head = self.head.next();
        self.len -= 1;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K: Ord + 'a> DoubleEndedIterator for Iter<'a, K> {
    #[inline]
    fn next_back(&mut self) -> Option<(&'a K, usize)> {
        // println!("len = {:?}", self.len);
        if self.len == 0 {
            return None;
        }

        if self.tail == self.head {
            return None;
        }

        let (k, v) = unsafe { (&(*self.tail.0).key, self.tail.count()) };
        self.tail = self.tail.prev();
        self.len -= 1;
        Some((k, v))
    }
}
