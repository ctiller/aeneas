//@ [!lean] skip
//! Regression test: boolean negation ([!b]) must extract to a [Bool] even where
//! Lean has no expected type. It used to be printed as [¬ b], a [Prop]: in
//! [take_left] below, the result of the [if] is bound by a [let] without a
//! type annotation, so Lean typed it as a [Prop] and then failed to synthesize
//! [Decidable take_left] for the condition [if take_left].
#![feature(register_tool)]
#![register_tool(verify)]

fn less(a: u32, b: u32) -> bool {
    a < b
}

pub fn take_left(p: usize, mid: usize, a: u32, b: u32) -> bool {
    let take_left = if p >= mid { false } else { !less(b, a) };
    if take_left {
        true
    } else {
        false
    }
}

pub fn not_bool(x: bool) -> bool {
    !x
}

pub fn not_u32(x: u32) -> u32 {
    !x
}

pub fn not_i32(x: i32) -> i32 {
    !x
}

#[verify::test]
fn test_bool_not() {
    assert!(take_left(0, 1, 1, 2));
    assert!(take_left(0, 1, 2, 2));
    assert!(!take_left(0, 1, 3, 2));
    assert!(!take_left(1, 1, 1, 2));
    assert!(not_bool(false));
    assert!(!not_bool(true));
    assert!(not_u32(0) == u32::MAX);
    assert!(not_i32(0) == -1);
}
