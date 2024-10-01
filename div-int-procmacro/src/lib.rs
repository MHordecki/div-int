//! Proc macro implementation for the crate [`div-int`](http://docs.rs/div-int).
extern crate proc_macro;

use std::fmt::{Display, Formatter};
use proc_macro2::{Span, TokenStream};
use proc_macro_error::{Diagnostic, Level};
use crate::ast::{DenominatorKind, Input, Operator};
use crate::number_literal::OutputType;

/// A compile-time constructor for `DivInt` literals.
///
/// There are two ways to invoke this macro:
/// * `div_int!(N / D)` constructs a `DivInt` with numerator `N` and denominator `D`.
/// * `div_int!(N * D)` constructs a `DivInt` with denominator `D` and the overall value of `N`.
///
/// # Examples
/// ```
/// use div_int::{div_int, DivInt};
///
/// // Numerator type inferred from context.
/// assert_eq!(div_int!(15 / 30), DivInt::<u8, 30>::from_numerator(15));
///
/// // Denominator inferred from context.
/// assert_eq!(div_int!(15 / _), DivInt::<u8, 30>::from_numerator(15));
///
/// // Explicit numerator type.
/// assert_eq!(div_int!(15u16 / 30), DivInt::<u16, 30>::from_numerator(15));
///
/// // Represent the given fraction.
/// assert_eq!(div_int!(1.5 * 30), DivInt::<u16, 30>::from_numerator(45));
/// assert_eq!(f64::from(div_int!(1.5u8 * 30)), 1.5f64);
///
/// // Represent the given fraction with a specific numerator type.
/// assert_eq!(div_int!(1.5u64 * 30), DivInt::<u64, 30>::from_numerator(45));
/// ```

#[proc_macro_error::proc_macro_error]
#[proc_macro]
pub fn div_int(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let tokens: TokenStream = tokens.into();
    let input = match Input::parse(&mut tokens.into_iter()) {
        Ok(input) => input,
        Err(err) => {
            if let Some(span) = err.span() {
                proc_macro_error::abort!(span, err);
            } else {
                proc_macro_error::abort!(Diagnostic::new(Level::Error, err.to_string()));
            }
        }
    };
    let code = match emit(&input) {
        Ok(code) => code,
        Err(err) => {
            if let Some(span) = err.span() {
                proc_macro_error::abort!(span, err);
            } else {
                proc_macro_error::abort!(Diagnostic::new(Level::Error, err.to_string()));
            }
        },
    };

    code.parse().expect("failed to produce valid macro output")
}

mod number_literal;
mod ast;

#[derive(Debug)]
enum EmitError {
    DivFormFloat(Span),
    NotDivisible(Span),
    OutsideTypeRange(Span, OutputType),
    MulFormInferredDenominator(Span),
}

impl EmitError {
    fn span(&self) -> Option<&Span> {
        match self {
            EmitError::DivFormFloat(span) => Some(span),
            EmitError::NotDivisible(span) => Some(span),
            EmitError::OutsideTypeRange(span, _) => Some(span),
            EmitError::MulFormInferredDenominator(span) => Some(span),
        }
    }
}

impl Display for EmitError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            EmitError::DivFormFloat(_) => f.write_str("Floating point number cannot be used with the \"div\" form of div_int"),
            EmitError::NotDivisible(_) => f.write_str("Denominator does not divide the provided numerator"),
            EmitError::OutsideTypeRange(_, OutputType::Unknown) =>
                f.write_str("Provided value is outside output type range"),
            EmitError::OutsideTypeRange(_, output_type) => {
                f.write_str("Provided value is outside output type range (")?;
                f.write_str(output_type.to_rust_type())?;
                f.write_str(")")
            }
            EmitError::MulFormInferredDenominator(_) =>
                f.write_str("Denominator must be provided when using the \"mul\" form of div_int"),
        }
    }
}

fn emit(input: &Input) -> Result<String, EmitError> {
    let numerator = match input.operator {
        Operator::Div => {
            if input.numerator.divider != 1 {
                return Err(EmitError::DivFormFloat(input.numerator.span));
            }
            input.numerator.value
        },
        Operator::Mul => {
            let divider = input.numerator.divider;
            let denominator = match input.denominator.kind {
                DenominatorKind::Inferred => return Err(EmitError::MulFormInferredDenominator(input.denominator.span)),
                DenominatorKind::Explicit(d) => d
            };

            let Some(value) = input.numerator.value.checked_mul(denominator as i128) else {
                return Err(EmitError::OutsideTypeRange(input.numerator.span, input.numerator.output_type));
            };

            if value % (divider as i128) != 0 {
                return Err(EmitError::NotDivisible(input.numerator.span));
            }

            value / (divider as i128)
        }
    };
    if !input.numerator.output_type.contains(numerator) {
        return Err(EmitError::OutsideTypeRange(input.numerator.span, input.numerator.output_type));
    }
    let output_type = input.numerator.output_type.to_rust_type();


    Ok(match input.denominator.kind {
        DenominatorKind::Explicit(d) => format!("::div_int::DivInt::<{output_type}, {d}>::from_numerator({numerator})"),
        DenominatorKind::Inferred => format!("::div_int::InferredDenominator::<{output_type}>::div_int({numerator})"),
    })
}


#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::{TokenStream, TokenTree};
    use assert_matches::assert_matches;

    fn to_tokens(input: &str) -> impl Iterator<Item = TokenTree> {
        let stream: TokenStream = input.parse().expect("Failed to parse test input");
        stream.into_iter()
    }

    fn parse_and_emit(input: &str) -> Result<String, EmitError> {
        let stream: TokenStream = input.parse().expect("Failed to parse test input");
        let input = Input::parse(&mut stream.into_iter()).expect("Failed to parse test input");
        emit(&input)
    }

    #[test]
    fn div_form() {
        assert_matches!(parse_and_emit("3 / 5").as_deref(), Ok("::div_int::DivInt::<_, 5>::from_numerator(3)"));
    }

    #[test]
    fn div_form_with_output_type() {
        assert_matches!(parse_and_emit("3u8 / 5").as_deref(), Ok("::div_int::DivInt::<u8, 5>::from_numerator(3)"));
    }

    #[test]
    fn div_form_with_implicit_types() {
        assert_matches!(parse_and_emit("3 / _").as_deref(), Ok("::div_int::InferredDenominator::<_>::div_int(3)"));
    }

    #[test]
    fn mul_form() {
        assert_matches!(parse_and_emit("1.5u16 * 10").as_deref(), Ok("::div_int::DivInt::<u16, 10>::from_numerator(15)"));
    }

    #[test]
    fn div_form_float() {
        assert_matches!(parse_and_emit("1.5 / 2"), Err(EmitError::DivFormFloat(_)));
    }

    #[test]
    fn outside_type_range() {
        assert_matches!(parse_and_emit("1.5u8 * 200"), Err(EmitError::OutsideTypeRange(_, OutputType::U8)));
    }

    #[test]
    fn mul_inferred_denominator() {
        assert_matches!(parse_and_emit("1 * _"), Err(EmitError::MulFormInferredDenominator(_)));
    }

    #[test]
    fn not_divisible() {
        assert_matches!(parse_and_emit("1.5 * 3"), Err(EmitError::NotDivisible(_)));
    }
}
