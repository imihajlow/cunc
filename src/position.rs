use std::fmt;

use pest::error::LineColLocation;

#[derive(Debug, Clone, PartialEq)]
pub enum Position {
    Unknown,
    Builtin,
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

impl Position {
    pub fn merge(&self, other: &Position) -> Position {
        use Position::*;
        match (self, other) {
            (Unknown, p) => Position::clone(p),
            (p, Unknown) => Position::clone(p),
            (Builtin, p) => Position::clone(p),
            (p, Builtin) => Position::clone(p),
            (Pos(a,b), Pos(c,d)) => {
                if before((*a,*b), (*c,*d)) {
                    Position::Span((*a,*b), (*c,*d))
                } else {
                    Position::Span((*c,*d), (*a,*b))
                }
            }
            (Pos(a,b), Span(f,t)) => {
                if before(*f, (*a,*b)) && before((*a,*b), *t) {
                    Span(*f,*t)
                } else if before((*a, *b), *f) {
                    Span((*a,*b), *t)
                } else {
                    Span(*f, (*a,*b))
                }
            }
            (Span(_,_), Pos(_,_)) => other.merge(self),
            (Span(f1,t1), Span(f2,t2)) => {
                Span(
                    if before(*f1, *f2) { *f1 } else { *f2 },
                    if before(*t1, *t2) { *t1 } else { *t2 }
                    )
            }
        }
    }
}

fn before(p1: (usize, usize), p2: (usize, usize)) -> bool {
    if p1.0 == p2.0 {
        p1.1 < p2.1
    } else {
        p1.0 < p2.0
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Position::Unknown => write!(f, "<unknown>"),
            Position::Builtin => write!(f, "<builtin>"),
            Position::Pos(r,c) => write!(f, "{}:{}", r, c),
            Position::Span((r1,c1),(r2,c2)) if r1 == r2 => write!(f, "{}:{}-{}", r1, c1, c2),
            Position::Span((r1,c1),(r2,c2)) => write!(f, "{}:{}-{}:{}", r1, c1, r2, c2),
        }
    }
}
