/// Extension trait providing a `.combinations(k)` method on slices.
pub trait Combinations {
    type Item;
    fn combinations(&self, k: usize) -> CombinationIter<'_, Self::Item>;
}

impl<T> Combinations for [T] {
    type Item = T;
    fn combinations(&self, k: usize) -> CombinationIter<'_, T> {
        CombinationIter::new(self, k)
    }
}

/// Iterator over all `k`-element combinations of a slice.
/// Each item is a `Vec<&T>`.
///
/// For slices with at most 64 elements, uses a bitmask (Gosper's hack)
/// internally for faster iteration. Falls back to index-based iteration
/// for larger slices.
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
    fn works_on_vec() {
        let v = vec![10, 20, 30];
        let got: Vec<Vec<i32>> = v
            .combinations(1)
            .map(|c| c.into_iter().cloned().collect())
            .collect();
        assert_eq!(got, [[10], [20], [30]]);
    }
}
