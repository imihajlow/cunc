use pest::error::LineColLocation;

pub type Position = LineColLocation;

pub fn position_from_span(span: &pest::Span) -> Position {
    LineColLocation::Span(span.start_pos().line_col(), span.end_pos().line_col())
}
