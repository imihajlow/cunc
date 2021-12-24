use std::fmt;

use pest::error::LineColLocation;

#[derive(Debug, Clone)]
pub enum Position {
    Pos(usize, usize),
    Span((usize, usize), (usize, usize))
}

pub fn position_from_span(span: &pest::Span) -> Position {
    Position::Span(span.start_pos().line_col(), span.end_pos().line_col())
}

pub fn position_from_linecol(p: LineColLocation) -> Position {
    match p {
        LineColLocation::Pos((l,c)) => Position::Pos(l, c),
        LineColLocation::Span(from, to) => Position::Span(from, to),
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Position::Pos(r,c) => write!(f, "{}:{}", r, c),
            Position::Span((r1,c1),(r2,c2)) if r1 == r2 => write!(f, "{}:{}-{}", r1, c1, c2),
            Position::Span((r1,c1),(r2,c2)) => write!(f, "{}:{}-{}:{}", r1, c1, r2, c2),
        }
    }
}
