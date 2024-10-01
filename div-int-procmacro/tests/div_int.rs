use div_int::div_int;

type DivInt<N, const D: u64> = div_int::DivInt<N, D>;

#[test]
fn div_implicit_numerator_type() {
    assert_eq!(div_int!(10 / 50), DivInt::<u16, 50>::from_numerator(10));
}

#[test]
fn div_explicit_numerator_type() {
    assert_eq!(div_int!(10u8 / 50), DivInt::<u8, 50>::from_numerator(10));
}

#[test]
fn div_explicit_denominator() {
    // Avoids a scenario where the macro always uses _ as a denominator but the Rust compiler
    // infers the const parameter from the context.
    let di = div_int!(10u8 / 50);
    assert_eq!(di.numerator(), 10);
}

#[test]
fn div_implicit_denominator() {
    assert_eq!(div_int!(10 / _), DivInt::<u8, 50>::from_numerator(10));
}

#[test]
fn mul_implicit_numerator_type() {
    assert_eq!(div_int!(10 * 50), DivInt::<u16, 50>::from_numerator(500));
}

#[test]
fn mul_float() {
    assert_eq!(div_int!(1.5 * 50), DivInt::<u16, 50>::from_numerator(75));
}

#[test]
fn mul_negative() {
    assert_eq!(div_int!(-1.5 * 50), DivInt::<i16, 50>::from_numerator(-75));
}

#[test]
fn mul_max_u64() {
    assert_eq!(div_int!(1u64 * 18446744073709551614), DivInt::<u64, 18446744073709551614>::from_numerator(18446744073709551614));
}