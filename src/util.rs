pub fn var_from_number(n: usize) -> String {
    if n < 26 {
        char::from_digit(n as u32 + 10, 36).unwrap().to_string()
    } else {
        format!("v{}", n)
    }
}
