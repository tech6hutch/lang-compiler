use std::{fmt, ops};

pub type CharAndPos = (char, Pos);

pub struct IterWithLineCol<I: Iterator<Item = char>> {
    iter: I,
    next_pos: Pos,
}

impl<I: Iterator<Item = char>> Iterator for IterWithLineCol<I> {
    type Item = CharAndPos;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|c| {
            let pos = self.next_pos.clone();
            if c == '\n' {
                self.next_pos.line += 1;
                self.next_pos.col = 0;
            } else {
                self.next_pos.col += 1;
            }
            (c, pos)
        })
    }
}

pub trait EnumerateLineCol: Iterator<Item = char> + Sized {
    fn enumerate_line_col(self) -> IterWithLineCol<Self>;
}

impl<I: Iterator<Item = char>> EnumerateLineCol for I {
    fn enumerate_line_col(self) -> IterWithLineCol<Self> {
        IterWithLineCol {
            iter: self,
            next_pos: Pos::default(),
        }
    }
}

/// A span of a source file, in lines and columns.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Span {
    /// Start of the span.
    pub start: Pos,
    /// Inclusive end of the span.
    pub end: Pos,
}

impl Span {
    /// A helper method to create a span over one position
    pub fn one(pos: Pos) -> Self {
        Self {
            start: pos,
            end: pos,
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Self { start, end } = self;
        f.write_str(if start.line == end.line {
            if start.col == end.col {
                format!("{}:{}", start.line, start.col)
            } else {
                format!("{}:{}-{}", start.line, start.col, end.col)
            }
        } else {
            format!("{} - {}", start, end)
        }.as_str())
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&format!("{:?} - {:?}", self.start, self.end))
    }
}

/// A position in a source file, as a line number and column number.
#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
}

impl Pos {
    /// Create a Pos that represents the next column in the same line
    pub fn next_col(&self) -> Self {
        Self {
            line: self.line,
            col: self.col + 1,
        }
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl fmt::Debug for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&format!("{}:{}", self.line, self.col))
    }
}

impl ops::Add for Pos {
    type Output = Self;
    fn add(self, other: Self) -> Self::Output {
        Self {
            line: self.line + other.line,
            col: self.col + other.col,
        }
    }
}

impl ops::Sub for Pos {
    type Output = Self;
    fn sub(self, other: Self) -> Self::Output {
        Self {
            line: self.line - other.line,
            col: self.col - other.col,
        }
    }
}

impl ops::AddAssign for Pos {
    fn add_assign(&mut self, other: Self) {
        self.line += other.line;
        self.col += other.col;
    }
}

impl ops::SubAssign for Pos {
    fn sub_assign(&mut self, other: Self) {
        self.line -= other.line;
        self.col -= other.col;
    }
}
