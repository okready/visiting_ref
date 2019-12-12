# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- [`Binary`](https://doc.rust-lang.org/stable/core/fmt/trait.Binary.html),
  [`LowerExp`](https://doc.rust-lang.org/stable/core/fmt/trait.LowerExp.html),
  [`LowerHex`](https://doc.rust-lang.org/stable/core/fmt/trait.LowerHex.html),
  [`Octal`](https://doc.rust-lang.org/stable/core/fmt/trait.Octal.html),
  [`Pointer`](https://doc.rust-lang.org/stable/core/fmt/trait.Pointer.html),
  [`UpperExp`](https://doc.rust-lang.org/stable/core/fmt/trait.UpperExp.html), and
  [`UpperHex`](https://doc.rust-lang.org/stable/core/fmt/trait.UpperHex.html) implementations for
  `VisitingRef` and `VisitingMut`.
- Unit tests for all custom string formatting trait implementations.
- Example in top-level crate documentation for using the crate to work around lifetime declaration
  limitations in certain scenarios when using asynchronous closures as function arguments.
- Table of contents in top-level crate documentation.

### Changed
- Remove `ManuallyDrop` wrapping from
  [`Debug`](https://doc.rust-lang.org/stable/core/fmt/trait.Debug.html) trait output for
  `VisitingRef` and `VisitingMut` for clarity and to avoid confusing `VisitingRef<T>` or
  `VisitingMut<T>` with `VisitingRef<ManuallyDrop<T>>` or `VisitingMut<ManuallyDrop<T>>`.
- Simplify `dev-dependencies` and adjust example code in documentation comments in response.

### Fixed
- Grammar in crate description.

## [0.1.0] - 2019-12-08
### Added
- Initial release.

[Unreleased]: https://github.com/okready/visiting_ref/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/okready/visiting_ref/releases/tag/v0.1.0
