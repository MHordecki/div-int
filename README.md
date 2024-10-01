# div-int

[![Crates.io](https://img.shields.io/crates/v/div-int.svg)](https://crates.io/crates/div-int)
[![API reference](https://docs.rs/div-int/badge.svg)](https://docs.rs/div-int/)

Rational numbers with a compile-time denominator.

This crate exports the `DivInt` struct, which is a wrapper around integers that are
semantically divided by a compile-time constant. It's designed for embedded applications
where floats are sometimes represented as rational numbers with a known denominator.

## Example

`DivInt<u8, 50>` is a number that's internally stored as a u8, but is semantically a rational
number which value is the stored number divided by 50:

```rust
use div_int::DivInt;

let di: DivInt<u8, 50> = DivInt::from_numerator(15);
assert_eq!(di.numerator(), 15);
assert_eq!(di.to_f64(), 0.3);
```

## Crate features

The crate is `no_std` by default. Optional features are:

* `serde` - adds serialization support.

License: MPL-2.0
