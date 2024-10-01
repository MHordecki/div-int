use std::fmt::{Display, Formatter};
use crate::number_literal::{NumberLiteral, NumberLiteralError};
use litrs::Literal;
use proc_macro2::{Span, TokenTree};

#[derive(Debug)]
pub(crate) enum Operator {
    Div,
    Mul,
}

impl Operator {
    fn parse(tokens: &mut impl Iterator<Item = TokenTree>) -> Result<Self, ParseError> {
        match tokens.next() {
            Some(TokenTree::Punct(punct)) if punct.as_char() == '*' => Ok(Self::Mul),
            Some(TokenTree::Punct(punct)) if punct.as_char() == '/' => Ok(Self::Div),
            Some(token) => Err(ParseError::InvalidOperator(token.span())),
            None => Err(ParseError::ExpectedOperator),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum DenominatorKind {
    Inferred,
    Explicit(u64),
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Denominator {
    pub(crate) span: Span,
    pub(crate) kind: DenominatorKind,
}

impl Denominator {
    fn parse(tokens: &mut impl Iterator<Item = TokenTree>) -> Result<Self, ParseError> {
        match tokens.next() {
            Some(TokenTree::Ident(ident)) if ident == "_" => Ok(Self {
                kind: DenominatorKind::Inferred,
                span: ident.span(),
            }),
            Some(TokenTree::Literal(lit_tok)) => match Literal::parse(lit_tok.to_string()) {
                Ok(Literal::Integer(lit)) => match lit.value::<u64>() {
                    Some(0) => Err(ParseError::ZeroDenominator(lit_tok.span())),
                    Some(value) => Ok(Self {
                        kind: DenominatorKind::Explicit(value),
                        span: lit_tok.span(),
                    }),
                    None => Err(ParseError::DenominatorOutOfRange(lit_tok.span())),
                },
                _ => Err(ParseError::InvalidDenominator(lit_tok.span())),
            },
            Some(token) => Err(ParseError::InvalidDenominator(token.span())),
            None => Err(ParseError::ExpectedDenominator),
        }
    }
}

#[derive(Debug)]
pub(crate) struct Input {
    pub(crate) numerator: NumberLiteral,
    pub(crate) operator: Operator,
    pub(crate) denominator: Denominator,
}

impl Input {
    pub(crate) fn parse(tokens: &mut impl Iterator<Item = TokenTree>) -> Result<Self, ParseError> {
        let numerator = NumberLiteral::parse(tokens)?;
        let operator = Operator::parse(tokens)?;
        let denominator = Denominator::parse(tokens)?;

        if let Some(token) = tokens.next() {
            return Err(ParseError::ExtraContent(token.span()));
        }

        Ok(Self {
            numerator,
            operator,
            denominator,
        })
    }
}

#[derive(Debug)]
pub(crate) enum ParseError {
    ExpectedNumerator,
    InvalidNumerator(Span),
    NumeratorOutOfRange(Span),
    ExpectedOperator,
    InvalidOperator(Span),
    ExtraContent(Span),
    InvalidNumeratorType(Span),
    ExpectedDenominator,
    InvalidDenominator(Span),
    DenominatorOutOfRange(Span),
    ZeroDenominator(Span),
}

impl ParseError {
    pub(crate) fn span(&self) -> Option<&Span> {
        match self {
            ParseError::ExpectedNumerator
            | ParseError::ExpectedOperator
            | ParseError::ExpectedDenominator => None,

            ParseError::InvalidNumerator(span)
            | ParseError::InvalidOperator(span)
            | ParseError::ExtraContent(span)
            | ParseError::InvalidDenominator(span)
            | ParseError::DenominatorOutOfRange(span)
            | ParseError::ZeroDenominator(span)
            | ParseError::InvalidNumeratorType(span)
            | ParseError::NumeratorOutOfRange(span) => Some(span),
        }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::ExpectedNumerator => f.write_str("Expected numerator here"),
            ParseError::InvalidNumerator(_) => f.write_str("Invalid numerator value"),
            ParseError::NumeratorOutOfRange(_) => f.write_str("Numerator value is out of range"),
            ParseError::ExpectedOperator => f.write_str("Expected `/` or `*` here"),
            ParseError::InvalidOperator(_) => f.write_str("Invalid operator (expected `/` or `*` here)"),
            ParseError::ExtraContent(_) => f.write_str("Unexpected content at the end"),
            ParseError::InvalidNumeratorType(_) => f.write_str("Invalid numerator type"),
            ParseError::ExpectedDenominator => f.write_str("Expected denominator here"),
            ParseError::InvalidDenominator(_) => f.write_str("Invalid denominator value"),
            ParseError::DenominatorOutOfRange(_) => f.write_str("Denominator value is out of range"),
            ParseError::ZeroDenominator(_) => f.write_str("Denominator value must not be zero"),
        }
    }
}

impl From<NumberLiteralError> for ParseError {
    fn from(err: NumberLiteralError) -> Self {
        match err {
            NumberLiteralError::Eof => Self::ExpectedNumerator,
            NumberLiteralError::Invalid(span) => Self::InvalidNumerator(span),
            NumberLiteralError::InvalidOutputType(span) => Self::InvalidNumeratorType(span),
            NumberLiteralError::OutOfRange(span) => Self::NumeratorOutOfRange(span),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::number_literal::OutputType;
    use assert_matches::assert_matches;
    use proc_macro2::TokenStream;

    fn to_tokens(input: &str) -> impl Iterator<Item = TokenTree> {
        let stream: TokenStream = input.parse().expect("Failed to parse test input");
        stream.into_iter()
    }

    #[test]
    fn parse_denominator_explicit() {
        assert_matches!(
            Denominator::parse(&mut to_tokens("123")),
            Ok(Denominator {
                kind: DenominatorKind::Explicit(123),
                ..
            })
        );
    }

    #[test]
    fn parse_denominator_inferred() {
        assert_matches!(
            Denominator::parse(&mut to_tokens("_")),
            Ok(Denominator {
                kind: DenominatorKind::Inferred,
                ..
            })
        );
    }

    #[test]
    fn parse_empty() {
        assert_matches!(
            Input::parse(&mut to_tokens("")),
            Err(ParseError::ExpectedNumerator)
        );
    }

    #[test]
    fn parse_without_operator() {
        assert_matches!(
            Input::parse(&mut to_tokens("12")),
            Err(ParseError::ExpectedOperator)
        );
    }

    #[test]
    fn parse_invalid_operator() {
        assert_matches!(
            Input::parse(&mut to_tokens("12 + 5")),
            Err(ParseError::InvalidOperator(_))
        );
    }

    #[test]
    fn parse_without_denominator() {
        assert_matches!(
            Input::parse(&mut to_tokens("12 *")),
            Err(ParseError::ExpectedDenominator)
        );
    }

    #[test]
    fn parse_invalid_denominator() {
        assert_matches!(
            Input::parse(&mut to_tokens("12 / 12e-1")),
            Err(ParseError::InvalidDenominator(_))
        );
    }

    #[test]
    fn parse_zero_denominator() {
        assert_matches!(
            Input::parse(&mut to_tokens("12 / 0")),
            Err(ParseError::ZeroDenominator(_))
        );
    }

    #[test]
    fn parse_input_mul() {
        assert_matches!(
            Input::parse(&mut to_tokens("123.4 * 50")),
            Ok(Input {
                numerator: NumberLiteral {
                    value: 1234,
                    divider: 10,
                    output_type: OutputType::Unknown,
                    span: _,
                },
                operator: Operator::Mul,
                denominator: Denominator {
                    kind: DenominatorKind::Explicit(50),
                    span: _,
                }
            })
        );
    }

    #[test]
    fn parse_input_div() {
        assert_matches!(
            Input::parse(&mut to_tokens("5i32 / _")),
            Ok(Input {
                numerator: NumberLiteral {
                    value: 5,
                    divider: 1,
                    output_type: OutputType::I32,
                    span: _,
                },
                operator: Operator::Div,
                denominator: Denominator {
                    kind: DenominatorKind::Inferred,
                    span: _,
                },
            })
        );
    }
}
