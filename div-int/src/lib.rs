//! Rational numbers with a compile-time denominator.
//!
//! This crate exports the [`DivInt`] struct, which is a wrapper around integers that are
//! semantically divided by a compile-time constant. It's designed for embedded applications
//! where floats are sometimes represented as rational numbers with a known denominator.
//!
//! # Example
//!
//! `DivInt<u8, 50>` is a number that's internally stored as a u8, but is semantically a rational
//! number which value is the stored number divided by 50:
//!
//! ```
//! use div_int::DivInt;
//!
//! let di: DivInt<u8, 50> = DivInt::from_numerator(15);
//! assert_eq!(di.numerator(), 15);
//! assert_eq!(di.to_f64(), 0.3);
//! ```
//!
//! # Crate features
//!
//! The crate is `no_std` by default. Optional features are:
//!
//! * `serde` - adds serialization support. [Read more][`serde`].
#![warn(missing_docs)]
#![no_std]
extern crate alloc;

use core::fmt::{Debug, Formatter};

#[cfg(feature = "serde")]
pub mod serde;

pub use div_int_procmacro::div_int;

/// Rational number with a compile-time denominator.
#[derive(Eq, PartialEq, Default, Ord, PartialOrd, Hash, Clone, Copy)]
pub struct DivInt<N, const D: u64>(N);

impl<N, const D: u64> DivInt<N, D> {
    /// Constructs the type using the provided number as the numerator.
    ///
    /// The effective value of the result is therefore `D` times smaller than the provided number.
    ///
    /// Consider using the convenience macro [`div_int!`] instead.
    pub const fn from_numerator(n: N) -> Self {
        Self(n)
    }
}

impl<N: FromF64Approx, const D: u64> DivInt<N, D> {
    /// Constructs a `DivInt` by approximating a floating-point number.
    ///
    /// This function will return `None` if the provided number is outside the value range of the
    /// `DivInt`.
    ///
    /// # Examples
    /// ```
    /// use div_int::{DivInt, div_int};
    ///
    /// assert_eq!(DivInt::<u8, 2>::from_f64_approx(1.5), Some(div_int!(3 / 2)));
    /// assert_eq!(DivInt::<u8, 2>::from_f64_approx(128.0), None);
    /// ```
    pub fn from_f64_approx(val: f64) -> Option<Self> {
        Some(Self::from_numerator(N::from_f64_approx(val * (D as f64))?))
    }
}

impl<N: Into<f64>, const D: u64> From<DivInt<N, D>> for f64 {
    fn from(value: DivInt<N, D>) -> Self {
        value.0.into() / (D as f64)
    }
}

impl<N: Copy + Into<f64>, const D: u64> DivInt<N, D> {
    /// Floating-point value of this `DivInt`.
    ///
    /// # Examples
    /// ```
    /// use div_int::DivInt;
    ///
    /// assert_eq!(DivInt::<u16, 200>::from_numerator(150).to_f64(), 0.75);
    /// ```
    pub fn to_f64(self) -> f64 {
        self.0.into() / (D as f64)
    }
}

impl<N: Copy, const D: u64> DivInt<N, D> {
    /// Numerator of this Ratio struct.
    ///
    /// # Examples
    /// ```
    /// use div_int::div_int;
    ///
    /// assert_eq!(div_int!(100 / 1024).numerator(), 100);
    /// ```
    pub const fn numerator(self) -> N {
        self.0
    }

    /// Denominator of this `DivInt`.
    ///
    /// This is a convenience function, as this value can be extracted from the type itself.
    ///
    /// # Examples
    /// ```
    /// use div_int::div_int;
    ///
    /// assert_eq!(div_int!(100 / 1024).denominator(), 1024);
    /// ```
    pub const fn denominator(self) -> u64 {
        D
    }
}

impl<N: Debug, const D: u64> Debug for DivInt<N, D> {
    /// Implements.
    ///
    /// # Example
    /// ```
    /// use div_int::DivInt;
    ///
    /// assert_eq!(format!("{:?}", DivInt::<_, 100>::from_numerator(5)), "div_int!(5 / 100)");
    /// ```
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str("div_int!(")?;
        self.0.fmt(f)?;
        f.write_str(" / ")?;
        D.fmt(f)?;
        f.write_str(")")
    }
}

macro_rules! impl_core_op {
    ($op:ident, $op_ident:ident) => {
        impl<N: core::ops::$op, const D: u64> core::ops::$op for DivInt<N, D> {
            type Output = DivInt<N::Output, D>;

            fn $op_ident(self, rhs: Self) -> Self::Output {
                DivInt::<N::Output, D>::from_numerator(self.0.$op_ident(rhs.0))
            }
        }
    };
}

impl_core_op!(Add, add);
impl_core_op!(Sub, sub);
impl_core_op!(Mul, mul);
impl_core_op!(Div, div);
impl_core_op!(Rem, rem);

macro_rules! impl_core_assign_op {
    ($op:ident, $op_ident:ident) => {
        impl<N: core::ops::$op, const D: u64> core::ops::$op for DivInt<N, D> {
            fn $op_ident(&mut self, rhs: Self) {
                self.0.$op_ident(rhs.0);
            }
        }
    };
}

impl_core_assign_op!(AddAssign, add_assign);
impl_core_assign_op!(SubAssign, sub_assign);
impl_core_assign_op!(MulAssign, mul_assign);
impl_core_assign_op!(DivAssign, div_assign);
impl_core_assign_op!(RemAssign, rem_assign);

impl<N: core::ops::Neg, const D: u64> core::ops::Neg for DivInt<N, D> {
    type Output = DivInt<N::Output, D>;

    fn neg(self) -> Self::Output {
        DivInt::<N::Output, D>::from_numerator(self.0.neg())
    }
}

impl<N: num_traits::WrappingAdd, const D: u64> DivInt<N, D> {
    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    /// ```
    /// use div_int::div_int;
    ///
    /// assert_eq!(div_int!(10u8 / 5).wrapping_add(div_int!(3u8 / 5)), div_int!(13u8 / 5));
    /// assert_eq!(div_int!(10u8 / 5).wrapping_add(div_int!(250u8 / 5)), div_int!(4u8 / 5));
    /// ```
    pub fn wrapping_add(self, other: Self) -> Self {
        Self(self.0.wrapping_add(&other.0))
    }
}

impl<N: num_traits::WrappingSub, const D: u64> DivInt<N, D> {
    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    /// ```
    /// use div_int::div_int;
    ///
    /// assert_eq!(div_int!(10u8 / 5).wrapping_sub(div_int!(3u8 / 5)), div_int!(7u8 / 5));
    /// assert_eq!(div_int!(10u8 / 5).wrapping_sub(div_int!(20u8 / 5)), div_int!(246u8 / 5));
    /// ```
    pub fn wrapping_sub(self, other: Self) -> Self {
        Self(self.0.wrapping_sub(&other.0))
    }
}

impl<N: num_traits::WrappingMul, const D: u64> DivInt<N, D> {
    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    /// ```
    /// use div_int::div_int;
    ///
    /// assert_eq!(div_int!(10u8 / 5).wrapping_mul(div_int!(3u8 / 5)), div_int!(30u8 / 5));
    /// assert_eq!(div_int!(10u8 / 5).wrapping_mul(div_int!(30u8 / 5)), div_int!(44u8 / 5));
    /// ```
    pub fn wrapping_mul(self, other: Self) -> Self {
        Self(self.0.wrapping_mul(&other.0))
    }
}

macro_rules! impl_num_op_trait {
    ($ty:ident, $op:ident) => {
        impl<N: num_traits::$ty, const D: u64> num_traits::$ty for DivInt<N, D> {
            fn $op(&self, v: &Self) -> Self {
                Self(self.0.$op(&v.0))
            }
        }
    }
}

impl_num_op_trait!(WrappingAdd, wrapping_add);
impl_num_op_trait!(WrappingSub, wrapping_sub);
impl_num_op_trait!(WrappingMul, wrapping_mul);

/// Helper trait for converting `f64` to integer types.
pub trait FromF64Approx: Sized {
    /// Constructs an integer type from a `f64`.
    ///
    /// Implementors must satisfy two invariants:
    ///   * For input values in range of the output type, return the closest value.
    ///   * For input values outside the range of the output type, return `None`.
    fn from_f64_approx(v: f64) -> Option<Self>;
}

macro_rules! impl_fromf64_approx {
    ($ty:ty, $fn_name:ident) => {
        impl FromF64Approx for $ty {
            fn from_f64_approx(v: f64) -> Option<Self> {
                num_traits::ToPrimitive::$fn_name(&v)
            }
        }
    };
}

impl_fromf64_approx!(u8, to_u8);
impl_fromf64_approx!(u16, to_u16);
impl_fromf64_approx!(u32, to_u32);
impl_fromf64_approx!(u64, to_u64);
impl_fromf64_approx!(i8, to_i8);
impl_fromf64_approx!(i16, to_i16);
impl_fromf64_approx!(i32, to_i32);
impl_fromf64_approx!(i64, to_i64);
impl_fromf64_approx!(f32, to_f32);
impl_fromf64_approx!(f64, to_f64);

/// A constructor for [`DivInt`] that infers the denominator.
///
/// In Rust 1.79, the following code does not compile (See [Rust issue #80528]):
///
/// ```ignore
/// use div_int::DivInt;
///
/// let r: DivInt<u8, 50> = DivInt::<u8, _>::from_numerator(12);
/// ```
///
/// This struct offers a workaround by using two separate generics for numerator and denominator:
///
/// ```
/// use div_int::{InferredDenominator, DivInt};
///
/// let r: DivInt<u8, 50> = InferredDenominator::<u8>::div_int(12);
/// ```
///
/// [Rust issue #80528]: https://github.com/rust-lang/rust/issues/80528
pub struct InferredDenominator<N>(core::marker::PhantomData<N>);

// https://github.com/rust-lang/rust/issues/80528
impl<N> InferredDenominator<N> {
    /// Constructs a [`DivInt`] instance.
    ///
    /// See the [struct-level documentation][InferredDenominator] for datils.
    pub fn div_int<const D: u64>(numerator: N) -> DivInt<N, D> {
        DivInt::from_numerator(numerator)
    }
}

