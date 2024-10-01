use litrs::Literal;
use proc_macro2::{Span, TokenTree};

#[derive(Debug, Clone, Copy)]
pub(crate) struct NumberLiteral {
    pub(crate) value: i128,
    pub(crate) divider: u128,
    pub(crate) span: Span,
    pub(crate) output_type: OutputType,
}

impl NumberLiteral {
    pub(crate) fn parse(tokens: &mut impl Iterator<Item = TokenTree>) -> Result<Self, NumberLiteralError> {
        let (sign, token) = match tokens.next() {
            Some(TokenTree::Punct(punct)) => {
                if punct.as_char() == '-' {
                    (false, tokens.next())
                } else {
                    return Err(NumberLiteralError::Invalid(punct.span()));
                }
            }
            token => (true, token),
        };

        match token {
            None => Err(NumberLiteralError::Eof),
            Some(TokenTree::Literal(lit_tok)) => match Literal::parse(lit_tok.to_string()) {
                Ok(Literal::Integer(lit)) => {
                    let Some(typ) = OutputType::from_str(lit.suffix()) else {
                        return Err(NumberLiteralError::InvalidOutputType(lit_tok.span()));
                    };
                    let Some(mut value): Option<i128> = lit.value() else {
                        return Err(NumberLiteralError::OutOfRange(lit_tok.span()));
                    };
                    if !sign {
                        value *= -1;
                    }

                    Ok(NumberLiteral {
                        value,
                        divider: 1,
                        span: lit_tok.span(),
                        output_type: typ,
                    })
                }
                Ok(Literal::Float(lit)) => {
                    let Some(typ) = OutputType::from_str(lit.suffix()) else {
                        return Err(NumberLiteralError::InvalidOutputType(lit_tok.span()));
                    };
                    let mut num: String = lit.integer_part().into();
                    if let Some(fractional_part) = lit.fractional_part() {
                        num.push_str(fractional_part);
                    };
                    let Ok(mut num): Result<i128, _> = num.parse() else {
                        return Err(NumberLiteralError::Invalid(lit_tok.span()));
                    };
                    if !sign {
                        num *= -1;
                    }

                    let mut exp: i16 = -(lit.fractional_part().unwrap_or_default().len() as i16);
                    if !lit.exponent_part().is_empty() {
                        match lit.exponent_part().strip_prefix("e") {
                            Some(exponent) => match exponent.parse::<i16>() {
                                Ok(e) => {
                                    exp += e;
                                }
                                Err(_) => return Err(NumberLiteralError::OutOfRange(lit_tok.span())),
                            },
                            None => return Err(NumberLiteralError::Invalid(lit_tok.span())),
                        };
                    }

                    let mut divider: u128 = 1;
                    match exp {
                        0.. => {
                            let Some(divider): Option<i128> = (10i128).checked_pow(exp as u32) else {
                                return Err(NumberLiteralError::OutOfRange(lit_tok.span()));
                            };
                            let Some(new_num) = num.checked_mul(divider) else {
                                return Err(NumberLiteralError::OutOfRange(lit_tok.span()));
                            };
                            num = new_num;
                        },
                        ..0 => {
                            let Some(d): Option<u128> = (10u128).checked_pow((-exp) as u32) else {
                                return Err(NumberLiteralError::OutOfRange(lit_tok.span()));
                            };
                            divider = d;
                        }
                    }

                    Ok(NumberLiteral {
                        value: num,
                        divider,
                        span: lit_tok.span(),
                        output_type: typ,
                    })
                }
                _ => Err(NumberLiteralError::Invalid(lit_tok.span())),
            },
            Some(token) => Err(NumberLiteralError::Invalid(token.span())),
        }
    }
}
#[derive(Debug)]
pub(crate) enum NumberLiteralError {
    Eof,
    Invalid(Span),
    InvalidOutputType(Span),
    OutOfRange(Span),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum OutputType {
    Unknown,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

impl OutputType {
    pub(crate) fn from_str(s: &str) -> Option<Self>{
        match s {
            "" => Some(Self::Unknown),
            "u8" => Some(Self::U8),
            "u16" => Some(Self::U16),
            "u32" => Some(Self::U32),
            "u64" => Some(Self::U64),
            "i8" => Some(Self::I8),
            "i16" => Some(Self::I16),
            "i32" => Some(Self::I32),
            "i64" => Some(Self::I64),
            _ => None,
        }
    }

    pub(crate) fn contains(self, value: i128) -> bool {
        use OutputType::*;
        match self {
            Unknown => i64::try_from(value).is_ok(),
            U8 => u8::try_from(value).is_ok(),
            U16 => u16::try_from(value).is_ok(),
            U32 => u32::try_from(value).is_ok(),
            U64 => u64::try_from(value).is_ok(),
            I8 => i8::try_from(value).is_ok(),
            I16 => i16::try_from(value).is_ok(),
            I32 => i32::try_from(value).is_ok(),
            I64 => i64::try_from(value).is_ok(),
        }
    }

    pub(crate) fn to_rust_type(self) -> &'static str {
        use OutputType::*;
        match self {
            Unknown => "_",
            U8 => "u8",
            U16 => "u16",
            U32 => "u32",
            U64 => "u64",
            I8 => "i8",
            I16 => "i16",
            I32 => "i32",
            I64 => "i64",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::TokenStream;
    use assert_matches::assert_matches;

    fn to_tokens(input: &str) -> impl Iterator<Item = TokenTree> {
        let stream: TokenStream = input.parse().expect("Failed to parse test input");
        stream.into_iter()
    }

    #[test]
    fn parse_int() {
        assert_matches!(
            NumberLiteral::parse(&mut to_tokens("1")),
            Ok(NumberLiteral {
                value: 1,
                divider: 1,
                output_type: OutputType::Unknown,
                span: _,
            })
        );
    }

    #[test]
    fn parse_int_with_suffix() {
        assert_matches!(
            NumberLiteral::parse(&mut to_tokens("123412341234u8")),
            Ok(NumberLiteral {
                value: 123412341234,
                divider: 1,
                output_type: OutputType::U8,
                span: _,
            })
        );
    }

    #[test]
    fn parse_float() {
        assert_matches!(
            NumberLiteral::parse(&mut to_tokens("12341234.1234123")),
            Ok(NumberLiteral {
                value: 123412341234123,
                divider: 10000000,
                output_type: OutputType::Unknown,
                span: _,
            })
        );
    }

    #[test]
    fn parse_float_with_suffix() {
        assert_matches!(
            NumberLiteral::parse(&mut to_tokens("0.1234u8")),
            Ok(NumberLiteral {
                value: 1234,
                divider: 10000,
                output_type: OutputType::U8,
                span: _,
            })
        );
    }

    #[test]
    fn parse_float_with_empty_fractional_part() {
        assert_matches!(
            NumberLiteral::parse(&mut to_tokens("12.")),
            Ok(NumberLiteral {
                value: 12,
                divider: 1,
                output_type: OutputType::Unknown,
                span: _,
            })
        );
    }

    #[test]
    fn parse_float_with_positive_exponent() {
        assert_matches!(
            NumberLiteral::parse(&mut to_tokens("12.5e1")),
            Ok(NumberLiteral {
                value: 125,
                divider: 1,
                output_type: OutputType::Unknown,
                span: _,
            })
        );
    }

    #[test]
    fn parse_float_with_negative_exponent() {
        assert_matches!(
            NumberLiteral::parse(&mut to_tokens("12.5e-1")),
            Ok(NumberLiteral {
                value: 125,
                divider: 100,
                output_type: OutputType::Unknown,
                span: _,
            })
        );
    }

    #[test]
    fn parse_int_with_exponent() {
        assert_matches!(
            NumberLiteral::parse(&mut to_tokens("125e-3")),
            Ok(NumberLiteral {
                value: 125,
                divider: 1000,
                output_type: OutputType::Unknown,
                span: _,
            })
        );
    }

    #[test]
    fn parse_negative() {
        assert_matches!(NumberLiteral::parse(&mut to_tokens("-43.21")),
            Ok(NumberLiteral {
                value: -4321,
                divider: 100,
                output_type: OutputType::Unknown,
                span: _,
            }));
    }

    #[test]
    fn parse_empty() {
        assert_matches!(NumberLiteral::parse(&mut to_tokens("")), Err(NumberLiteralError::Eof));
    }

    #[test]
    fn parse_wrong_punct() {
        assert_matches!(NumberLiteral::parse(&mut to_tokens("+123")), Err(NumberLiteralError::Invalid(_)));
    }

    #[test]
    fn parse_wrong_literal() {
        assert_matches!(NumberLiteral::parse(&mut to_tokens("\"123\"")), Err(NumberLiteralError::Invalid(_)));
    }

    #[test]
    fn parse_invalid_output_type() {
        assert_matches!(NumberLiteral::parse(&mut to_tokens("123u34")), Err(NumberLiteralError::InvalidOutputType(_)));
        assert_matches!(NumberLiteral::parse(&mut to_tokens("12.3u34")), Err(NumberLiteralError::InvalidOutputType(_)));
    }

    #[test]
    fn parse_out_of_range() {
        assert_matches!(NumberLiteral::parse(&mut to_tokens("3402823669209384634633746074317682114550")), Err(NumberLiteralError::OutOfRange(_)));
    }

    #[test]
    fn parse_exponent_out_of_range() {
        assert_matches!(NumberLiteral::parse(&mut to_tokens("32e99999999")), Err(NumberLiteralError::OutOfRange(_)));
    }
}
