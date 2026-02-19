# k-combinations

Efficient iterator over k-element combinations of a slice, with no dependencies.

For slices with at most 64 elements, uses a bitmask ([Gosper's hack](https://en.wikipedia.org/wiki/Combinatorial_number_system#Applications)) for fast iteration. Falls back to index-based iteration for larger slices.

## Usage

Add to your project:

```sh
cargo add k-combinations
```

```rust
use combinations::Combinations;

let items = [1, 2, 3, 4];

// All pairs
for combo in items.combinations(2) {
    println!("{combo:?}");
}
// [&1, &2], [&1, &3], [&2, &3], [&1, &4], [&2, &4], [&3, &4]

// Works on Vec too
let v = vec!["a", "b", "c"];
let pairs: Vec<Vec<&&str>> = v.combinations(2).collect();
```

## Range of sizes

Iterate over combinations of multiple sizes with `combinations_range`:

```rust
use combinations::Combinations;

let items = [1, 2, 3];

// All subsets of size 1 or 2
for combo in items.combinations_range(1..=2) {
    println!("{combo:?}");
}

// All 2^n subsets (power set)
assert_eq!(items.combinations_range(..).count(), 8);
```

## Zero-allocation iteration

Reuse a buffer across calls with `next_into`, similar to `BufReader::read_line`:

```rust
use combinations::Combinations;

let items = [1, 2, 3, 4];
let mut iter = items.combinations(2);
let mut buf = Vec::new();
while iter.next_into(&mut buf) {
    // buf is reused — no allocation after the first call
    println!("{buf:?}");
}
```

## License

MIT
