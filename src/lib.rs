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

/// Iterator over all `k`-element combinations of a slice, yielded in
/// lexicographic order. Each item is a `Vec<&T>`.
pub struct CombinationIter<'a, T> {
    slice: &'a [T],
    indices: Vec<usize>,
    done: bool,
}

impl<'a, T> CombinationIter<'a, T> {
    fn new(slice: &'a [T], k: usize) -> Self {
        if k > slice.len() {
            return Self { slice, indices: Vec::new(), done: true };
        }
        Self {
            slice,
            indices: (0..k).collect(),
            done: false,
        }
    }
}

impl<'a, T> Iterator for CombinationIter<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let k = self.indices.len();
        let n = self.slice.len();

        let result: Vec<&'a T> = self.indices.iter().map(|&i| &self.slice[i]).collect();

        // Advance to the next combination.
        // Find the rightmost index that can be incremented.
        let mut i = k;
        while i > 0 {
            i -= 1;
            if self.indices[i] < n - k + i {
                self.indices[i] += 1;
                for j in (i + 1)..k {
                    self.indices[j] = self.indices[j - 1] + 1;
                }
                return Some(result);
            }
        }

        // No index could be incremented — this was the last combination.
        self.done = true;
        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn choose_2() {
        let v = vec!["hej", "på", "dig"];
        let got: Vec<Vec<&&str>> = v.combinations(2).collect();
        assert_eq!(got, vec![
            vec![&"hej", &"på"],
            vec![&"hej", &"dig"],
            vec![&"på", &"dig"],
        ]);
    }

    #[test]
    fn choose_0() {
        let got: Vec<Vec<i32>> = [1, 2, 3].combinations(0)
            .map(|c| c.into_iter().cloned().collect()).collect();
        assert_eq!(got, vec![vec![]]);
    }

    #[test]
    fn choose_all() {
        let got: Vec<Vec<i32>> = [1, 2, 3].combinations(3)
            .map(|c| c.into_iter().cloned().collect()).collect();
        assert_eq!(got, vec![vec![1, 2, 3]]);
    }

    #[test]
    fn k_exceeds_len() {
        let got: Vec<Vec<i32>> = [1, 2].combinations(5)
            .map(|c| c.into_iter().cloned().collect()).collect();
        assert!(got.is_empty());
    }

    #[test]
    fn count() {
        // C(6, 3) = 20
        assert_eq!([0; 6].combinations(3).count(), 20);
    }

    #[test]
    fn lexicographic_order() {
        let items = [0, 1, 2, 3];
        let got: Vec<Vec<i32>> = items.combinations(2)
            .map(|c| c.into_iter().cloned().collect()).collect();
        assert_eq!(got, vec![
            vec![0, 1], vec![0, 2], vec![0, 3],
            vec![1, 2], vec![1, 3],
            vec![2, 3],
        ]);
    }

    #[test]
    fn empty_slice() {
        let empty: &[i32] = &[];
        let got: Vec<Vec<i32>> = empty.combinations(0)
            .map(|c| c.into_iter().cloned().collect()).collect();
        assert_eq!(got, vec![vec![]]);
        assert!(empty.combinations(1).collect::<Vec<_>>().is_empty());
    }

    #[test]
    fn works_on_vec() {
        let v = vec![10, 20, 30];
        let got: Vec<Vec<i32>> = v.combinations(1)
            .map(|c| c.into_iter().cloned().collect()).collect();
        assert_eq!(got, vec![vec![10], vec![20], vec![30]]);
    }
}
