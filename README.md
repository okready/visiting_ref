visiting_ref
============

Containers that asynchronously returns ownership of a value to another context upon exiting
scope.

[![Latest Version](https://img.shields.io/crates/v/visiting_ref.svg)](https://crates.io/crates/visiting_ref)
[![Released API docs](https://docs.rs/visiting_ref/badge.svg)](https://docs.rs/visiting_ref)
![MIT/Apache-2.0 licensed](https://img.shields.io/crates/l/visiting_ref.svg)
[![Rustc Version 1.25+](https://img.shields.io/badge/rustc-1.39+-lightgray.svg)](https://blog.rust-lang.org/2019/11/07/Rust-1.39.0.html)
[![Build Status](https://travis-ci.org/okready/visiting_ref.svg?branch=master)](https://travis-ci.org/okready/visiting_ref)

- [Documentation](https://docs.rs/visiting_ref)
- [Release notes](https://github.com/okready/visiting_ref/releases)

This crate provides `VisitingRef` and `VisitingMut`, two container types that effectively
allow for safe "borrowing" of values through temporary transference of ownership between two
separate contexts. These types wrap a given value, only allowing a reference to the value to be
taken while the container is active. Upon exiting scope, the owned value is automatically sent
back to another context asynchronously.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
visiting_ref = "0.1"
```

Now you can use `VisitingRef` and `VisitingMut` types in your code:

```rust
use visiting_ref::VisitingRef;
```

More details and example code can be found in the [crate
documentation](https://docs.rs/visiting_ref).

## Rust Version Support

The minimum supported Rust version is 1.39 due to use of `futures` channels.

## `no_std` Support

This crate does not require `std`, but it does require `alloc` due to the use of `futures` oneshot
channels. No features need to be disabled for use with `no_std` crates.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
