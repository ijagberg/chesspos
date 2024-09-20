use self::consts::*;
use std::{
    error::Error,
    fmt::{Debug, Display},
    str::FromStr,
};
use File::*;
use Rank::*;

mod consts;
pub mod prelude;

/// A chess position, consisting of a `File` and a `Rank`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Position(File, Rank);

impl Position {
    const fn construct(file: File, rank: Rank) -> Self {
        Self(file, rank)
    }

    /// Create a new `Position`.
    pub const fn new(file: File, rank: Rank) -> Self {
        Self::construct(file, rank)
    }

    /// Create an iterator over all positions, in the order `A1, A2, A3, ..., H7, H8`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let positions: Vec<Position> = Position::increasing_iter().collect();
    /// assert_eq!(&positions[..5], vec![A1, A2, A3, A4, A5]);
    /// assert_eq!(&positions[61..], vec![H6, H7, H8]);
    /// ```
    pub fn increasing_iter() -> impl Iterator<Item = Self> {
        INCREASING_A1_A2.iter().copied()
    }

    /// Get the `File` component of this `Position`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(C3.file(), File::C);
    /// ```
    pub const fn file(&self) -> File {
        self.0
    }

    /// Get the `Rank` component of this `Position`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(F8.rank(), Rank::Eight);
    /// ```
    pub const fn rank(&self) -> Rank {
        self.1
    }

    /// Get the [Manhattan distance](https://en.wikipedia.org/wiki/Taxicab_geometry) between this `Position` and `other`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(B5.manhattan_distance_to(E5), 3);
    /// assert_eq!(B5.manhattan_distance_to(E7), 5);
    /// ```
    pub fn manhattan_distance_to(self, other: Self) -> usize {
        let file_dist = self.file().as_u8().abs_diff(other.file().as_u8());
        let rank_dist = self.rank().as_u8().abs_diff(other.rank().as_u8());
        usize::from(file_dist + rank_dist)
    }

    /// Get the `Position` one rank above `self`, or `None` if no such position exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(A2.up(), Some(A3));
    /// assert_eq!(C8.up(), None); // no position above rank 8
    /// ```
    pub fn up(&self) -> Option<Self> {
        let file = self.file();
        let rank = self.rank().up()?;
        Some(Self::construct(file, rank))
    }

    /// Get the `Position` one rank above and one file to the right of `self`, or `None` if no such position exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(D2.up_right(), Some(E3));
    /// assert_eq!(A8.up_right(), None); // no position above rank 8
    /// assert_eq!(H1.up_right(), None); // no position to the right of file H
    /// ```
    pub fn up_right(&self) -> Option<Self> {
        let file = self.file().right()?;
        let rank = self.rank().up()?;
        Some(Self::construct(file, rank))
    }

    /// Get the `Position` one file to the right of `self`, or `None` if no such position exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(F5.right(), Some(G5));
    /// assert_eq!(H2.right(), None); // no position to the right of file H
    /// ```
    pub fn right(&self) -> Option<Self> {
        let file = self.file().right()?;
        let rank = self.rank();
        Some(Self::construct(file, rank))
    }

    /// Get the `Position` one rank below and one file to the right of `self`, or `None` if no such position exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(B7.down_right(), Some(C6));
    /// assert_eq!(A1.down_right(), None); // no position below rank 1
    /// assert_eq!(H5.down_right(), None); // no position to the right of file H
    /// ```
    pub fn down_right(&self) -> Option<Self> {
        let file = self.file().right()?;
        let rank = self.rank().down()?;
        Some(Self::construct(file, rank))
    }

    /// Get the `Position` one rank below `self`, or `None` if no such position exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(B7.down(), Some(B6));
    /// assert_eq!(A1.down(), None); // no position below rank 1
    /// ```
    pub fn down(&self) -> Option<Self> {
        let file = self.file();
        let rank = self.rank().down()?;
        Some(Self::construct(file, rank))
    }

    /// Get the `Position` one rank below and one file to the left of `self`, or `None` if no such position exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(B7.down_left(), Some(A6));
    /// assert_eq!(C1.down_left(), None); // no position below rank 1
    /// assert_eq!(A5.down_left(), None); // no position to the left of file A
    /// ```
    pub fn down_left(&self) -> Option<Self> {
        let file = self.file().left()?;
        let rank = self.rank().down()?;
        Some(Self::construct(file, rank))
    }

    /// Get the `Position` one file to the left of `self`, or `None` if no such position exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(B7.left(), Some(A7));
    /// assert_eq!(A1.left(), None); // no position to the left of file A
    /// ```
    pub fn left(&self) -> Option<Self> {
        let file = self.file().left()?;
        let rank = self.rank();
        Some(Self::construct(file, rank))
    }

    /// Get the `Position` one rank above and one file to the left of `self`, or `None` if no such position exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(B7.up_left(), Some(A8));
    /// assert_eq!(A1.up_left(), None); // no position to the left of file A
    /// assert_eq!(F8.up_left(), None); // no position above rank 8
    /// ```
    pub fn up_left(&self) -> Option<Self> {
        let file = self.file().left()?;
        let rank = self.rank().up()?;
        Some(Self::construct(file, rank))
    }

    /// Return an iterator over the neighbors of `self`, going clockwise.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let neighbors_of_e4: Vec<Position> = A3.neighbors().collect();
    /// assert_eq!(neighbors_of_e4, vec![A4, B4, B3, B2, A2]);
    /// ```
    pub fn neighbors(&self) -> impl Iterator<Item = Self> {
        use std::iter::once;
        once(self.up())
            .chain(once(self.up_right()))
            .chain(once(self.right()))
            .chain(once(self.down_right()))
            .chain(once(self.down()))
            .chain(once(self.down_left()))
            .chain(once(self.left()))
            .chain(once(self.up_left()))
            .flatten()
    }
}

impl From<(File, Rank)> for Position {
    fn from((file, rank): (File, Rank)) -> Self {
        Self::new(file, rank)
    }
}

impl Debug for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.file(), self.rank())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidPositionError {
    InvalidLength,
    InvalidFile(InvalidFileError),
    InvalidRank(InvalidRankError),
}

impl Display for InvalidPositionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                InvalidPositionError::InvalidLength => "invalid length".to_string(),
                InvalidPositionError::InvalidFile(e) => e.to_string(),
                InvalidPositionError::InvalidRank(e) => e.to_string(),
            }
        )
    }
}

impl Error for InvalidPositionError {}

impl From<InvalidFileError> for InvalidPositionError {
    fn from(value: InvalidFileError) -> Self {
        Self::InvalidFile(value)
    }
}

impl From<InvalidRankError> for InvalidPositionError {
    fn from(value: InvalidRankError) -> Self {
        Self::InvalidRank(value)
    }
}

impl FromStr for Position {
    type Err = InvalidPositionError;

    /// Parse
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();
        let file = chars.next().ok_or(InvalidPositionError::InvalidLength)?;
        let rank = chars.next().ok_or(InvalidPositionError::InvalidLength)?;

        if chars.next().is_some() {
            // length of iterator should be exactly 2
            return Err(InvalidPositionError::InvalidLength);
        }

        let file = File::try_from_char(file)?;
        let rank = Rank::try_from_char(rank)?;

        Ok(Self::new(file, rank))
    }
}

/// The file component of a chess position.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum File {
    A,
    B,
    C,
    D,
    E,
    F,
    G,
    H,
}

impl File {
    /// Get the `File` to the left of `self`, or `None` if no such file exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(File::F.left(), Some(File::E));
    /// assert_eq!(File::A.left(), None);
    /// ```
    pub fn left(self) -> Option<Self> {
        let v = self.as_u8();
        if v > 0 {
            Self::try_from_u8(v - 1).ok()
        } else {
            None
        }
    }

    /// Returns an iterator over the files to the left of, and including `self`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let left: Vec<File> = File::E.walk_left().collect();
    /// assert_eq!(left, vec![File::E, File::D, File::C, File::B, File::A]);
    /// ```
    pub fn walk_left(self) -> impl Iterator<Item = Self> {
        ALL_FILES[..=usize::from(self.as_u8()) - 1]
            .iter()
            .copied()
            .rev()
    }

    /// Get the `File` to the right of `self`, or `None` if no such file exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(File::F.right(), Some(File::G));
    /// assert_eq!(File::H.right(), None);
    /// ```
    pub fn right(self) -> Option<Self> {
        Self::try_from_u8(self.as_u8() + 1).ok()
    }

    /// Returns an iterator over the files to the right of, and including `self`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let right: Vec<File> = File::E.walk_right().collect();
    /// assert_eq!(right, vec![File::E, File::F, File::G, File::H]);
    /// ```
    pub fn walk_right(self) -> impl Iterator<Item = Self> {
        ALL_FILES[usize::from(self.as_u8()) - 1..].iter().copied()
    }

    /// Create an iterator over all positions in the `File`, in ascending order.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let ranks: Vec<Position> = File::A.iter().collect();
    /// assert_eq!(ranks, vec![A1, A2, A3, A4, A5, A6, A7, A8]);
    /// ```
    pub fn iter(self) -> impl DoubleEndedIterator<Item = Position> {
        ALL_RANKS
            .iter()
            .map(move |&rank| Position::construct(self, rank))
    }

    #[allow(unused)]
    pub(crate) fn add_offset(self, offset: i32) -> Option<Self> {
        let v = i32::from(self.as_u8()) + offset;
        Self::try_from_u8(u8::try_from(v).ok()?).ok()
    }

    pub(crate) fn as_u8(self) -> u8 {
        match self {
            A => 1,
            B => 2,
            C => 3,
            D => 4,
            E => 5,
            F => 6,
            G => 7,
            H => 8,
        }
    }

    pub(crate) fn try_from_u8(v: u8) -> Result<Self, InvalidFileError> {
        Ok(match v {
            1 => A,
            2 => B,
            3 => C,
            4 => D,
            5 => E,
            6 => F,
            7 => G,
            8 => H,
            _ => return Err(InvalidFileError::InvalidFile),
        })
    }

    pub(crate) fn try_from_char(v: char) -> Result<Self, InvalidFileError> {
        Ok(match v {
            'a' | 'A' => A,
            'b' | 'B' => B,
            'c' | 'C' => C,
            'd' | 'D' => D,
            'e' | 'E' => E,
            'f' | 'F' => F,
            'g' | 'G' => G,
            'h' | 'H' => H,
            _ => return Err(InvalidFileError::InvalidFile),
        })
    }
}

impl Display for File {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            A => "a",
            B => "b",
            C => "c",
            D => "d",
            E => "e",
            F => "f",
            G => "g",
            H => "h",
        };
        write!(f, "{}", s)
    }
}

/// Error returned when parsing a `File` fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidFileError {
    InvalidFile,
}

impl Display for InvalidFileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                InvalidFileError::InvalidFile => "invalid file",
            }
        )
    }
}

impl Error for InvalidFileError {}

impl PartialOrd for File {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for File {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_u8().cmp(&other.as_u8())
    }
}

/// The rank component of a chess position.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Rank {
    One,
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
    Eight,
}

impl Rank {
    /// Get the `Rank` above `self`, or `None` if no such rank exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(Rank::One.up(), Some(Rank::Two));
    /// assert_eq!(Rank::Eight.up(), None);
    /// ```
    pub fn up(self) -> Option<Self> {
        Self::try_from_u8(self.as_u8() + 1).ok()
    }

    /// Returns an iterator over the ranks above, and including `self`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let up: Vec<Rank> = Rank::Six.walk_up().collect();
    /// assert_eq!(up, vec![Rank::Six, Rank::Seven, Rank::Eight]);
    /// ```
    pub fn walk_up(self) -> impl Iterator<Item = Self> {
        ALL_RANKS[usize::from(self.as_u8()) - 1..].iter().copied()
    }

    /// Get the `Rank` below `self`, or `None` if no such rank exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(Rank::Seven.down(), Some(Rank::Six));
    /// assert_eq!(Rank::One.down(), None);
    /// ```
    pub fn down(self) -> Option<Self> {
        let v = self.as_u8();
        if v > 0 {
            Self::try_from_u8(v - 1).ok()
        } else {
            None
        }
    }

    /// Returns an iterator over the ranks below, and including `self`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let down: Vec<Rank> = Rank::Three.walk_down().collect();
    /// assert_eq!(down, vec![Rank::Three, Rank::Two, Rank::One]);
    /// ```
    pub fn walk_down(self) -> impl Iterator<Item = Self> {
        ALL_RANKS[..=usize::from(self.as_u8()) - 1]
            .iter()
            .copied()
            .rev()
    }

    /// Create an iterator over all positions in the `Rank`, in ascending order.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let ranks: Vec<Position> = Rank::Four.iter().collect();
    /// assert_eq!(ranks, vec![A4, B4, C4, D4, E4, F4, G4, H4]);
    /// ```
    pub fn iter(self) -> impl DoubleEndedIterator<Item = Position> {
        ALL_FILES
            .iter()
            .map(move |&file| Position::construct(file, self))
    }

    pub(crate) fn as_u8(self) -> u8 {
        match self {
            One => 1,
            Two => 2,
            Three => 3,
            Four => 4,
            Five => 5,
            Six => 6,
            Seven => 7,
            Eight => 8,
        }
    }

    pub(crate) fn try_from_u8(v: u8) -> Result<Self, InvalidRankError> {
        Ok(match v {
            1 => One,
            2 => Two,
            3 => Three,
            4 => Four,
            5 => Five,
            6 => Six,
            7 => Seven,
            8 => Eight,
            _ => return Err(InvalidRankError::InvalidRank),
        })
    }

    pub(crate) fn try_from_char(v: char) -> Result<Self, InvalidRankError> {
        Ok(match v {
            '1' => One,
            '2' => Two,
            '3' => Three,
            '4' => Four,
            '5' => Five,
            '6' => Six,
            '7' => Seven,
            '8' => Eight,
            _ => return Err(InvalidRankError::InvalidRank),
        })
    }
}

impl Display for Rank {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            One => "1",
            Two => "2",
            Three => "3",
            Four => "4",
            Five => "5",
            Six => "6",
            Seven => "7",
            Eight => "8",
        };
        write!(f, "{}", s)
    }
}

/// Error returned when parsing a `Rank` fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidRankError {
    InvalidRank,
}

impl Display for InvalidRankError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                InvalidRankError::InvalidRank => "invalid rank",
            }
        )
    }
}

impl Error for InvalidRankError {}

impl PartialOrd for Rank {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rank {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_u8().cmp(&other.as_u8())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn directions_test() {
        assert_eq!(E4.up(), Some(E5));
        assert_eq!(E4.up_right(), Some(F5));
        assert_eq!(E4.right(), Some(F4));
        assert_eq!(E4.down_right(), Some(F3));
        assert_eq!(E4.down(), Some(E3));
        assert_eq!(E4.down_left(), Some(D3));
        assert_eq!(E4.left(), Some(D4));
        assert_eq!(E4.up_left(), Some(D5));

        for pos in Position::increasing_iter() {
            if let Some(up) = pos.up() {
                assert_eq!(up.down(), Some(pos));
            }
            if let Some(up_right) = pos.up_right() {
                assert_eq!(up_right.down_left(), Some(pos));
            }
            if let Some(right) = pos.right() {
                assert_eq!(right.left(), Some(pos));
            }
            if let Some(down_right) = pos.down_right() {
                assert_eq!(down_right.up_left(), Some(pos));
            }
            if let Some(down) = pos.down() {
                assert_eq!(down.up(), Some(pos));
            }
            if let Some(down_left) = pos.down_left() {
                assert_eq!(down_left.up_right(), Some(pos));
            }
            if let Some(left) = pos.left() {
                assert_eq!(left.right(), Some(pos));
            }
            if let Some(up_left) = pos.up_left() {
                assert_eq!(up_left.down_right(), Some(pos));
            }
        }
    }

    #[test]
    fn file_directions_test() {
        assert_eq!(
            File::E.walk_left().collect::<Vec<_>>(),
            vec![File::E, File::D, File::C, File::B, File::A]
        );
    }

    #[test]
    fn file_iter_test() {
        let positions: Vec<Position> = File::C.iter().collect();
        assert_eq!(positions, vec![C1, C2, C3, C4, C5, C6, C7, C8]);

        // reversible
        let positions: Vec<Position> = File::C.iter().rev().collect();
        assert_eq!(positions, vec![C8, C7, C6, C5, C4, C3, C2, C1]);

        // peekable
        let mut i = File::C.iter().peekable();
        let pos = i.peek();
        assert!(matches!(pos, Some(Position(File::C, Rank::One))));
    }

    #[test]
    fn rank_iter_test() {
        let positions: Vec<Position> = Rank::Seven.iter().collect();
        assert_eq!(positions, vec![A7, B7, C7, D7, E7, F7, G7, H7]);

        // reversible
        let positions: Vec<Position> = Rank::Seven.iter().rev().collect();
        assert_eq!(positions, vec![H7, G7, F7, E7, D7, C7, B7, A7]);

        // peekable
        let mut i = Rank::Seven.iter().peekable();
        let pos = i.peek();
        assert!(matches!(pos, Some(Position(File::A, Rank::Seven))));
    }

    #[test]
    fn manhattan_distance_to_test() {
        assert_eq!(E4.manhattan_distance_to(E3), 1);
        assert_eq!(E4.manhattan_distance_to(A1), 7);
        assert_eq!(E4.manhattan_distance_to(A8), 8);
        assert_eq!(E4.manhattan_distance_to(H1), 6);
        assert_eq!(E4.manhattan_distance_to(H8), 7);
    }

    #[test]
    fn parse_position_test() {
        assert_eq!(E4, "e4".parse().unwrap());
        assert_eq!(
            "abc".parse::<Position>(),
            Err(InvalidPositionError::InvalidLength)
        );
        assert_eq!(
            "a5d".parse::<Position>(),
            Err(InvalidPositionError::InvalidLength)
        );
        assert!(matches!(
            "aa".parse::<Position>(),
            Err(InvalidPositionError::InvalidRank(_))
        ));
    }
}
