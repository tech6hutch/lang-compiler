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

/// For when you want to access a field of or call a method on values of different types, but
/// can't abstract over them in any other way, this macro lets you shove them all into one
/// (pseudo) match arm. Allows regular match arms before and after the "magic" one.
///
/// The "==>" is just a unique symbol to disambiguate which match arm is the one you want to apply
/// the magic to.
macro_rules! each_case {
    // I don't know of any way to accept either a field or a method in the same rule :/

    // each.method()
    (match $m:path {
        $( $pre_arm_pat:pat => $pre_arm_case:expr, )*
        ==> $( $each_pat:path )|+ => each.$each_case:ident(),
        $( $post_arm_pat:pat => $post_arm_case:expr, )*
    }) => {
        match $m {
            $( $pre_arm_pat => $pre_arm_case, )*
            $( $each_pat(each) => each.$each_case(), )+
            $( $post_arm_pat => $post_arm_case, )*
        }
    };

    // each.field
    (match $m:path {
        $( $pre_arm_pat:pat => $pre_arm_case:expr, )*
        ==> $( $each_pat:path )|+ => each.$each_case:ident,
        $( $post_arm_pat:pat => $post_arm_case:expr, )*
    }) => {
        match $m {
            $( $pre_arm_pat => $pre_arm_case, )*
            $( $each_pat(each) => each.$each_case, )+
            $( $post_arm_pat => $post_arm_case, )*
        }
    };
}

pub fn s_if_plural<T: IntoIterator>(list: T) -> &'static str {
    if list.into_iter().count() == 1 { "" } else { "s" }
}

pub fn space_quote_nonempty<S: AsRef<str>>(s: S) -> String {
    if s.as_ref().is_empty() {
        "".to_string()
    } else {
        space_quote(s)
    }
}

pub fn space_quote<S: AsRef<str>>(s: S) -> String {
    [" '", s.as_ref(), "'"].concat()
}
