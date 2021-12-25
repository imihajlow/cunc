use std::cmp;

pub fn var_from_number(n: usize) -> String {
    if n < 26 {
        char::from_digit(n as u32 + 10, 36).unwrap().to_string()
    } else {
        format!("v{}", n)
    }
}

pub fn max_options<T>(a: Option<T>, b: Option<T>) -> Option<T>
    where T: Ord + Copy {
    match (a, b) {
        (Some(x), Some(y)) => Some(cmp::max(x, y)),
        (Some(x), None) => Some(x),
        (None, Some(y)) => Some(y),
        _ => None
    }       
}
