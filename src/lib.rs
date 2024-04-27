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
    fn construct(file: File, rank: Rank) -> Self {
        Self(file, rank)
    }

    /// Create a new `Position`.
    pub fn new(file: File, rank: Rank) -> Self {
        Self::construct(file, rank)
    }

    /// Create an iterator over all positions in the given `File`, in ascending order.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let ranks: Vec<Position> = Position::file_iter(File::A).collect();
    /// assert_eq!(ranks, vec![A1, A2, A3, A4, A5, A6, A7, A8]);
    /// ```
    pub fn file_iter(file: File) -> impl Iterator<Item = Self> {
        ALL_RANKS
            .iter()
            .map(move |&rank| Self::construct(file, rank))
    }

    /// Create an iterator over all positions in the given `Rank`, in ascending order.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let files: Vec<Position> = Position::rank_iter(Rank::Four).collect();
    /// assert_eq!(files, vec![A4, B4, C4, D4, E4, F4, G4, H4]);
    /// ```
    pub fn rank_iter(rank: Rank) -> impl Iterator<Item = Self> {
        ALL_FILES
            .iter()
            .map(move |&file| Self::construct(file, rank))
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
    pub fn file(&self) -> File {
        self.0
    }

    /// Get the `Rank` component of this `Position`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(F8.rank(), Rank::Eight);
    /// ```
    pub fn rank(&self) -> Rank {
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
    pub fn manhattan_distance_to(&self, other: Self) -> usize {
        let file_dist = u8::from(self.file()).abs_diff(u8::from(other.file()));
        let rank_dist = u8::from(self.rank()).abs_diff(u8::from(other.rank()));
        (file_dist + rank_dist) as usize
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

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();
        let file = chars.next().ok_or(InvalidPositionError::InvalidLength)?;
        let rank = chars.next().ok_or(InvalidPositionError::InvalidLength)?;
        if chars.next().is_some() {
            return Err(InvalidPositionError::InvalidLength);
        }

        let file = File::try_from(file)?;
        let rank = Rank::try_from(rank)?;

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
    pub fn left(&self) -> Option<Self> {
        let v = u8::from(*self);
        if v > 0 {
            Self::try_from(v - 1).ok()
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
    pub fn walk_left(&self) -> impl Iterator<Item = Self> {
        ALL_FILES[..=usize::from(u8::from(*self))]
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
    pub fn right(&self) -> Option<Self> {
        Self::try_from(u8::from(*self) + 1).ok()
    }

    /// Returns an iterator over the files to the right of, and including `self`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let right: Vec<File> = File::E.walk_right().collect();
    /// assert_eq!(right, vec![File::E, File::F, File::G, File::H]);
    /// ```
    pub fn walk_right(&self) -> impl Iterator<Item = Self> {
        ALL_FILES[usize::from(u8::from(*self))..].iter().copied()
    }

    #[allow(unused)]
    pub(crate) fn add_offset(&self, offset: i32) -> Option<Self> {
        let v = (u8::from(*self)) as i32 + offset;
        Self::try_from(u8::try_from(v).ok()?).ok()
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

impl TryFrom<char> for File {
    type Error = InvalidFileError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            'a' | 'A' => Self::A,
            'b' | 'B' => Self::B,
            'c' | 'C' => Self::C,
            'd' | 'D' => Self::D,
            'e' | 'E' => Self::E,
            'f' | 'F' => Self::F,
            'g' | 'G' => Self::G,
            'h' | 'H' => Self::H,
            _ => return Err(InvalidFileError::InvalidFile),
        })
    }
}

impl From<File> for u8 {
    fn from(value: File) -> Self {
        match value {
            A => 0,
            B => 1,
            C => 2,
            D => 3,
            E => 4,
            F => 5,
            G => 6,
            H => 7,
        }
    }
}

impl From<File> for usize {
    fn from(value: File) -> Self {
        usize::from(u8::from(value))
    }
}

impl TryFrom<u8> for File {
    type Error = InvalidFileError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        use File::*;
        Ok(match value {
            0 => A,
            1 => B,
            2 => C,
            3 => D,
            4 => E,
            5 => F,
            6 => G,
            7 => H,
            _ => return Err(InvalidFileError::InvalidFile),
        })
    }
}

impl PartialOrd for File {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for File {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        u8::from(*self).cmp(&u8::from(*other))
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
    pub fn up(&self) -> Option<Self> {
        Self::try_from(u8::from(*self) + 1).ok()
    }

    /// Returns an iterator over the ranks above, and including `self`.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// let up: Vec<Rank> = Rank::Six.walk_up().collect();
    /// assert_eq!(up, vec![Rank::Six, Rank::Seven, Rank::Eight]);
    /// ```
    pub fn walk_up(&self) -> impl Iterator<Item = Self> {
        ALL_RANKS[usize::from(u8::from(*self))..].iter().copied()
    }

    /// Get the `Rank` below `self`, or `None` if no such rank exists.
    ///
    /// ## Example
    /// ```rust
    /// # use chesspos::prelude::*;
    /// assert_eq!(Rank::Seven.down(), Some(Rank::Six));
    /// assert_eq!(Rank::One.down(), None);
    /// ```
    pub fn down(&self) -> Option<Self> {
        let v = u8::from(*self);
        if v > 0 {
            Self::try_from(v - 1).ok()
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
    pub fn walk_down(&self) -> impl Iterator<Item = Self> {
        ALL_RANKS[..=usize::from(u8::from(*self))]
            .iter()
            .copied()
            .rev()
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

impl TryFrom<char> for Rank {
    type Error = InvalidRankError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            '1' => Self::One,
            '2' => Self::Two,
            '3' => Self::Three,
            '4' => Self::Four,
            '5' => Self::Five,
            '6' => Self::Six,
            '7' => Self::Seven,
            '8' => Self::Eight,
            _ => return Err(InvalidRankError::InvalidRank),
        })
    }
}

impl From<Rank> for u8 {
    fn from(value: Rank) -> Self {
        match value {
            One => 0,
            Two => 1,
            Three => 2,
            Four => 3,
            Five => 4,
            Six => 5,
            Seven => 6,
            Eight => 7,
        }
    }
}

impl From<Rank> for usize {
    fn from(value: Rank) -> Self {
        usize::from(u8::from(value))
    }
}

impl TryFrom<u8> for Rank {
    type Error = InvalidRankError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        use Rank::*;
        Ok(match value {
            0 => One,
            1 => Two,
            2 => Three,
            3 => Four,
            4 => Five,
            5 => Six,
            6 => Seven,
            7 => Eight,
            _ => return Err(InvalidRankError::InvalidRank),
        })
    }
}

impl PartialOrd for Rank {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rank {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        u8::from(*self).cmp(&u8::from(*other))
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
        let positions: Vec<Position> = Position::file_iter(File::C).collect();
        assert_eq!(positions, vec![C1, C2, C3, C4, C5, C6, C7, C8]);
    }

    #[test]
    fn rank_iter_test() {
        let positions: Vec<Position> = Position::rank_iter(Rank::Seven).collect();
        assert_eq!(positions, vec![A7, B7, C7, D7, E7, F7, G7, H7]);
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
