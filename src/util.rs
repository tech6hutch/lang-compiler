use std::iter::once;
use unicode_names2::name;

/// Returns `Some(t)` if the `bool` is `true`, or `None` otherwise.
#[inline]
pub fn if_some<T>(b: bool, t: T) -> Option<T> {
    if b { Some(t) } else { None }
}

/// Returns `Some(f())` if the `bool` is `true`, or `None` otherwise.
#[inline]
pub fn if_then<T, F: FnOnce() -> T>(b: bool, f: F) -> Option<T> {
    if b { Some(f()) } else { None }
}

/// Returns `f()` if the `bool` is `true`, or `None` otherwise.
///
/// This is useful because Rust still doesn't have a way to chain `if` and `if`-`let`,
/// at least on stable.
#[inline]
pub fn if_and_then<T, F: FnOnce() -> Option<T>>(b: bool, f: F) -> Option<T> {
    if b { f() } else { None }
}

/// Includes quotes and a trailing space.
pub fn format_first_char_name(s: &str) -> String {
    format_char_name(s.chars().next().unwrap())
}

/// Includes quotes and a trailing space.
pub fn format_char_name(c: char) -> String {
    name(c)
        .map(|n| once("'")
            .chain(n)
            .chain(once("' "))
            .collect::<String>())
        .unwrap_or("".to_string())
}
