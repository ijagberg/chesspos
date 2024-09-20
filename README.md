# chesspos

Useful structs and constants for representing chess board positions.

## Position

The main point of this library is the `Position` struct, which represents a position on a chess board.

```rust
use chesspos::prelude::*;

// each position is defined as a const,
// and can be referred to like this:
let a4 = A4;

// the Position struct has various methods
// useful for chess programming
assert_eq!(B4, a4.right().unwrap()); // get the position to the right of A4
assert!(a4.left().is_none()); // no position to the left of A4
```

## Rank & File

There's also a `Rank` and a `File` enum, which is useful for traversal and iteration.

```rust
use chesspos::prelude::*;

assert_eq!(File::G.iter().collect(), vec![G1, G2, G3, G4, G5, G6, G7, G8]);
assert_eq!(Rank::Two.iter().collect(), vec![A2, B2, C2, D2, E2, F2, G2, H2]);
```
