use std::ops::{Bound, RangeBounds};

/// Extension trait providing combination methods on slices.
///
/// ```
/// use combinations::Combinations;
///
/// let items = [1, 2, 3, 4];
///
/// // All pairs
/// let pairs: Vec<Vec<&i32>> = items.combinations(2).collect();
/// assert_eq!(pairs.len(), 6);
///
/// // Works on Vec too
/// let v = vec!["a", "b", "c"];
/// for combo in v.combinations(2) {
///     assert_eq!(combo.len(), 2);
/// }
/// ```
pub trait Combinations {
    type Item;

    /// Returns an iterator over all `k`-element combinations.
    ///
    /// ```
    /// use combinations::Combinations;
    ///
    /// let items = ["a", "b", "c"];
    /// let got: Vec<Vec<&&str>> = items.combinations(2).collect();
    /// assert_eq!(got, [vec![&"a", &"b"], vec![&"a", &"c"], vec![&"b", &"c"]]);
    ///
    /// // k=0 yields one empty combination
    /// assert_eq!(items.combinations(0).count(), 1);
    ///
    /// // k > len yields nothing
    /// assert!(items.combinations(10).next().is_none());
    /// ```
    fn combinations(&self, k: usize) -> CombinationIter<'_, Self::Item>;

    /// Returns an iterator over combinations of all sizes within `range`.
    ///
    /// Accepts any [`RangeBounds<usize>`]: `0..=k`, `1..3`, `..`, etc.
    /// Combinations are yielded in order of increasing size.
    ///
    /// ```
    /// use combinations::Combinations;
    ///
    /// // All subsets of size 1 or 2
    /// let items = [1, 2, 3];
    /// let got: Vec<Vec<&i32>> = items.combinations_range(1..=2).collect();
    /// assert_eq!(got.len(), 6); // C(3,1) + C(3,2) = 3 + 3
    ///
    /// // All 2^3 = 8 subsets
    /// assert_eq!(items.combinations_range(..).count(), 8);
    /// ```
    fn combinations_range(&self, range: impl RangeBounds<usize>) -> CombinationRangeIter<'_, Self::Item>;
}

impl<T> Combinations for [T] {
    type Item = T;
    fn combinations(&self, k: usize) -> CombinationIter<'_, T> {
        CombinationIter::new(self, k)
    }
    fn combinations_range(&self, range: impl RangeBounds<usize>) -> CombinationRangeIter<'_, T> {
        CombinationRangeIter::new(self, range)
    }
}

/// Iterator over all `k`-element combinations of a slice.
/// Each item is a `Vec<&T>`.
///
/// For slices with at most 64 elements, uses a bitmask (Gosper's hack)
/// internally for faster iteration. Falls back to index-based iteration
/// for larger slices.
///
/// Created by [`Combinations::combinations`].
///
/// ```
/// use combinations::Combinations;
///
/// let items = [10, 20, 30];
/// let mut iter = items.combinations(2);
///
/// assert_eq!(iter.next(), Some(vec![&10, &20]));
/// assert_eq!(iter.next(), Some(vec![&10, &30]));
/// assert_eq!(iter.next(), Some(vec![&20, &30]));
/// assert_eq!(iter.next(), None);
/// ```
pub struct CombinationIter<'a, T> {
    slice: &'a [T],
    state: State,
}

enum State {
    Bitmask {
        current: u64,
        limit: u64,
        done: bool,
    },
    Index {
        indices: Vec<usize>,
        done: bool,
    },
}

/// Mask with the lowest `bits` bits set.
fn low_mask(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else if bits == 0 {
        0
    } else {
        (1u64 << bits) - 1
    }
}

impl<'a, T> CombinationIter<'a, T> {
    /// Fills `buf` with the next combination, returning `true` if one was
    /// produced. The buffer is cleared before each call, so callers can
    /// reuse the same `Vec` across iterations to avoid repeated allocation.
    ///
    /// ```
    /// use combinations::Combinations;
    ///
    /// let items = [1, 2, 3];
    /// let mut iter = items.combinations(2);
    /// let mut buf = Vec::new();
    /// while iter.next_into(&mut buf) {
    ///     println!("{buf:?}"); // no allocation after the first call
    /// }
    /// ```
    pub fn next_into(&mut self, buf: &mut Vec<&'a T>) -> bool {
        buf.clear();
        match &mut self.state {
            State::Bitmask {
                current,
                limit,
                done,
            } => {
                if *done {
                    return false;
                }

                let v = *current;

                let mut bits = v;
                while bits != 0 {
                    let i = bits.trailing_zeros();
                    buf.push(&self.slice[i as usize]);
                    bits &= bits - 1;
                }

                if v == 0 {
                    *done = true;
                    return true;
                }

                let t = v | (v - 1);
                if let Some(t1) = t.checked_add(1) {
                    let next = t1 | (((!t & t1) - 1) >> (v.trailing_zeros() + 1));
                    if next > *limit {
                        *done = true;
                    } else {
                        *current = next;
                    }
                } else {
                    *done = true;
                }

                true
            }
            State::Index { indices, done } => {
                if *done {
                    return false;
                }

                let k = indices.len();
                let n = self.slice.len();

                buf.extend(indices.iter().map(|&i| &self.slice[i]));

                let mut i = k;
                while i > 0 {
                    i -= 1;
                    if indices[i] < n - k + i {
                        indices[i] += 1;
                        for j in (i + 1)..k {
                            indices[j] = indices[j - 1] + 1;
                        }
                        return true;
                    }
                }

                *done = true;
                true
            }
        }
    }

    fn new(slice: &'a [T], k: usize) -> Self {
        let n = slice.len();
        if n <= 64 {
            if k > n {
                return Self {
                    slice,
                    state: State::Bitmask {
                        current: 0,
                        limit: 0,
                        done: true,
                    },
                };
            }
            let limit = low_mask(n as u32);
            let start = low_mask(k as u32);
            Self {
                slice,
                state: State::Bitmask {
                    current: start,
                    limit,
                    done: false,
                },
            }
        } else {
            if k > n {
                return Self {
                    slice,
                    state: State::Index {
                        indices: Vec::new(),
                        done: true,
                    },
                };
            }
            Self {
                slice,
                state: State::Index {
                    indices: (0..k).collect(),
                    done: false,
                },
            }
        }
    }
}

impl<'a, T> Iterator for CombinationIter<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = Vec::new();
        if self.next_into(&mut buf) {
            Some(buf)
        } else {
            None
        }
    }
}

/// Iterator over combinations of multiple sizes within a range.
///
/// Created by [`Combinations::combinations_range`].
///
/// ```
/// use combinations::Combinations;
///
/// let items = [1, 2, 3];
/// let mut iter = items.combinations_range(0..=1);
///
/// assert_eq!(iter.next(), Some(vec![]));       // k=0
/// assert_eq!(iter.next(), Some(vec![&1]));     // k=1
/// assert_eq!(iter.next(), Some(vec![&2]));
/// assert_eq!(iter.next(), Some(vec![&3]));
/// assert_eq!(iter.next(), None);
/// ```
pub struct CombinationRangeIter<'a, T> {
    slice: &'a [T],
    current_k: usize,
    end_k: usize,
    inner: CombinationIter<'a, T>,
}

impl<'a, T> CombinationRangeIter<'a, T> {
    fn new(slice: &'a [T], range: impl RangeBounds<usize>) -> Self {
        let start_k = match range.start_bound() {
            Bound::Included(&s) => s,
            Bound::Excluded(&s) => s + 1,
            Bound::Unbounded => 0,
        };
        let end_k = match range.end_bound() {
            Bound::Included(&e) => e.min(slice.len()),
            Bound::Excluded(&0) => {
                return Self {
                    slice,
                    current_k: 1,
                    end_k: 0,
                    inner: CombinationIter::new(slice, 0),
                };
            }
            Bound::Excluded(&e) => (e - 1).min(slice.len()),
            Bound::Unbounded => slice.len(),
        };
        let current_k = start_k;
        let inner = CombinationIter::new(slice, current_k);
        Self {
            slice,
            current_k,
            end_k,
            inner,
        }
    }

    /// Fills `buf` with the next combination, returning `true` if one was
    /// produced. See [`CombinationIter::next_into`] for details.
    ///
    /// ```
    /// use combinations::Combinations;
    ///
    /// let items = [1, 2, 3];
    /// let mut iter = items.combinations_range(1..=2);
    /// let mut buf = Vec::new();
    /// let mut count = 0;
    /// while iter.next_into(&mut buf) {
    ///     count += 1;
    /// }
    /// assert_eq!(count, 6); // C(3,1) + C(3,2)
    /// ```
    pub fn next_into(&mut self, buf: &mut Vec<&'a T>) -> bool {
        loop {
            if self.inner.next_into(buf) {
                return true;
            }
            if self.current_k >= self.end_k {
                return false;
            }
            self.current_k += 1;
            self.inner = CombinationIter::new(self.slice, self.current_k);
        }
    }
}

impl<'a, T> Iterator for CombinationRangeIter<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = Vec::new();
        if self.next_into(&mut buf) {
            Some(buf)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn choose_2() {
        let v = vec!["hej", "på", "dig"];
        let got: Vec<Vec<&&str>> = v.combinations(2).collect();
        assert_eq!(
            got,
            vec![
                vec![&"hej", &"på"],
                vec![&"hej", &"dig"],
                vec![&"på", &"dig"],
            ]
        );
    }

    #[test]
    fn choose_0() {
        let got: Vec<Vec<i32>> = [1, 2, 3]
            .combinations(0)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        assert_eq!(got, [[] as [i32; 0]]);
    }

    #[test]
    fn choose_all() {
        let got: Vec<Vec<i32>> = [1, 2, 3]
            .combinations(3)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        assert_eq!(got, [[1, 2, 3]]);
    }

    #[test]
    fn k_exceeds_len() {
        let got: Vec<Vec<i32>> = [1, 2]
            .combinations(5)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        assert!(got.is_empty());
    }

    #[test]
    fn count() {
        // C(6, 3) = 20
        assert_eq!([0; 6].combinations(3).count(), 20);
    }

    #[test]
    fn correct_combinations() {
        let items = [0, 1, 2, 3];
        let got: Vec<Vec<i32>> = items
            .combinations(2)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        // Co-lexicographic order (Gosper's hack / bitmask ascending)
        assert_eq!(got, [
            [0, 1], [0, 2], [1, 2],
            [0, 3], [1, 3],
            [2, 3],
        ]);
    }

    #[test]
    fn empty_slice() {
        let empty: &[i32] = &[];
        let got: Vec<Vec<i32>> = empty
            .combinations(0)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        assert_eq!(got, [[] as [i32; 0]]);
        assert!(empty.combinations(1).collect::<Vec<_>>().is_empty());
    }

    #[test]
    fn next_into_reuses_buffer() {
        let items = [1, 2, 3];
        let mut iter = items.combinations(2);
        let mut buf = Vec::new();
        let mut got = Vec::new();
        while iter.next_into(&mut buf) {
            got.push(buf.iter().map(|&&x| x).collect::<Vec<i32>>());
        }
        assert_eq!(got, [[1, 2], [1, 3], [2, 3]]);
    }

    #[test]
    fn range_inclusive() {
        let got: Vec<Vec<i32>> = [1, 2, 3]
            .combinations_range(0..=2)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        // k=0, then k=1, then k=2
        assert_eq!(got, [
            vec![],
            vec![1], vec![2], vec![3],
            vec![1, 2], vec![1, 3], vec![2, 3],
        ]);
    }

    #[test]
    fn range_exclusive() {
        let got: Vec<Vec<i32>> = [1, 2, 3]
            .combinations_range(1..3)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        assert_eq!(got, [
            vec![1], vec![2], vec![3],
            vec![1, 2], vec![1, 3], vec![2, 3],
        ]);
    }

    #[test]
    fn range_full() {
        // All 2^3 = 8 subsets of [1,2,3]
        let got: Vec<Vec<i32>> = [1, 2, 3]
            .combinations_range(..)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        assert_eq!(got, [
            vec![],
            vec![1], vec![2], vec![3],
            vec![1, 2], vec![1, 3], vec![2, 3],
            vec![1, 2, 3],
        ]);
    }

    #[test]
    fn range_empty() {
        let got: Vec<Vec<&i32>> = [1, 2].combinations_range(5..=6).collect();
        assert!(got.is_empty());
    }

    #[test]
    fn works_on_vec() {
        let v = vec![10, 20, 30];
        let got: Vec<Vec<i32>> = v
            .combinations(1)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        assert_eq!(got, [[10], [20], [30]]);
    }
}
