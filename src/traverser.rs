use std::collections::HashMap;
use lazy_static::lazy_static;

#[derive(Copy, Clone)]
pub struct EscSeq {
    pub replace: char,
    pub desc: &'static str,
}
impl EscSeq {
    fn new(replace: char, desc: &'static str) -> Self{
        Self { replace, desc }
    }
}

lazy_static! {
    pub static ref ESCAPE_SEQS: HashMap<&'static str, EscSeq> = [
        (r"\n", EscSeq::new('\n', "newline")),
        (r"\t", EscSeq::new('\t', "tab")),
        ("\\\"", EscSeq::new('"', "double quote")),
        (r"\\", EscSeq::new('\\', "backslash")),
    ].iter().copied().collect();

    pub static ref ALLOWED_ESCAPE_CHARS: Box<[char]> = ESCAPE_SEQS
        .iter()
        .map(|(seq, _)| {
            assert_eq!('\\', seq.chars().next().unwrap());
            assert_eq!(seq.chars().count(), 2, "this needs to be rethought");
            seq.chars().last().unwrap()
        })
        .collect();
}
