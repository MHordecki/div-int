//! Additional functionality for serializing/deserializing `DivInt` structs with Serde.
//!
//! By default, `DivInt` is serialized using its semantic value, i.e. as floating-point
//! numbers. For example, a `div_int!(35 / 20)` is serialized as `1.75`.
//!
//! This serialization scheme is lossy. If you want precise behavior, you can serialize `DivInt`
//! using the numerator only by configuring Serde using the [`as_numerator`] module.

use alloc::format;
use core::fmt::{Display, Formatter};
use serde::{Serializer, Deserializer};
use crate::{DivInt, FromF64Approx};

/// Custom Serde serializer/deserializer module that uses numerator as the serialized value.
///
/// The default Serialize/Deserialize implementation of [`DivInt`] serializes the struct as a
/// floating point number. With this serializer (and Serde's `with` attribute) you can override
/// the built-in behavior and serialize `DivInt` as a numerator instead.
///
/// # Examples
/// ```
/// use serde::{Deserialize, Serialize};
/// use div_int::{DivInt, div_int};
///
/// #[derive(Serialize, Deserialize, Debug, Eq, PartialEq)]
/// struct Test {
///   #[serde(with="div_int::serde::as_numerator")]
///   num: DivInt<u16, 1024>,
/// }
///
/// assert_eq!(serde_json::to_string(&Test{num: div_int!(100 / 1024) }).unwrap(), r#"{"num":100}"#);
/// assert_eq!(serde_json::from_str::<Test>(r#"{"num": 123}"#).unwrap(), Test {num: div_int!(123 / 1024)});
/// ```
pub mod as_numerator {
    use crate::DivInt;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    /// Serde [serializer function] for `DivInt` that uses the numerator as the serialized value.
    ///
    /// [serializer function]: https://serde.rs/field-attrs.html#serialize_with
    pub fn serialize<S: Serializer, N: Serialize, const D: u64>(di: &DivInt<N, D>, s: S) -> Result<S::Ok, S::Error> {
        di.0.serialize(s)
    }

    /// Serde [deserializer function] for `DivInt` that expects the numerator as the deserialized.
    ///
    /// [deserializer function]: https://serde.rs/field-attrs.html#deserialize_with
    pub fn deserialize<'de, De, N: Deserialize<'de>, const D: u64>(d: De) -> Result<DivInt<N, D>, De::Error>
    where
        De: Deserializer<'de>,
    {
        Ok(DivInt::from_numerator(N::deserialize(d)?))
    }
}


struct OutOfRangeError(f64, &'static str, u64);

impl Display for OutOfRangeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str("value ")?;
        self.0.fmt(f)?;
        f.write_str(" does not fit into DivInt<")?;
        f.write_str(self.1)?;
        f.write_str(", ")?;
        self.2.fmt(f)?;
        f.write_str(">")
    }
}

#[cfg(feature="serde")]
impl<N: Copy + Into<f64>, const D: u64> ::serde::Serialize for DivInt<N, D> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ::serde::Serializer
    {
        self.to_f64().serialize(serializer)
    }
}

impl<'de, N: FromF64Approx, const D: u64> ::serde::Deserialize<'de> for DivInt<N, D> {
    fn deserialize<De>(deserializer: De) -> Result<Self, De::Error>
    where
        De: Deserializer<'de>
    {
        let f = f64::deserialize(deserializer)?;
        match DivInt::<N, D>::from_f64_approx(f) {
            Some(v) => Ok(v),
            None => Err(serde::de::Error::custom(OutOfRangeError(f, core::any::type_name::<N>(), D)))
        }
    }
}

#[cfg(test)]
#[cfg(feature="serde")]
mod tests {
    use serde::{Deserialize, Serialize};
    use super::*;

    #[test]
    fn serialize() {
        #[derive(Serialize, Debug, Eq, PartialEq)]
        struct Test {
            num: DivInt<u8, 2>,
        }

        assert_eq!(serde_json::to_string(&Test{ num: DivInt::<u8, 2>::from_numerator(3) }).unwrap(), r#"{"num":1.5}"#);
    }

    #[test]
    fn deserialize() {
        #[derive(Deserialize, Debug, Eq, PartialEq)]
        struct Test {
            num: DivInt<u8, 2>,
        }

        assert_eq!(serde_json::from_str::<Test>(r#"{"num":1.5}"#).unwrap(), Test{num: DivInt::<u8, 2>::from_numerator(3)});
    }
}