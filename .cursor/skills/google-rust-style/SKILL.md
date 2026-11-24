---
name: google-rust-style
description: Follow the Google Rust style guide when writing or editing Rust. Use for any .rs file in this repo.
paths: ["**/*.rs"]
---

# Google Rust style

Follow the [Google Rust style guide](https://google.github.io/styleguide/rustguide.html) when you write or edit Rust.

`rustfmt` and Clippy (`-D warnings`) stay required. Do not add a repo-wide `rustfmt.toml` to force `imports_granularity`. Split a `use` list when you are already editing that import, and in new code.

Sections marked Chrome, Android, or Fuchsia in the guide do not apply here. The rest does, including the parts that are not checked below.

## Checks

These pasta rules fail the build. Each name is the `pasta:ignore` token.

| Rule | What it flags |
| --- | --- |
| `rust_glob_import` | A glob import. `super::*`, a path that contains `prelude`, and `pub use` are allowed. |
| `rust_use_granularity` | A `use` list whose braces contain `::`. Import each module in its own statement. `use foo::bar::{Bar, Baz}` is one module and is fine. |
| `rust_catch_unwind` | A call to `panic::catch_unwind`. |
| `rust_unstable_feature` | `#![feature(...)]` or `#[feature(...)]`. `#[cfg(feature = "...")]` is a Cargo feature and is fine. |

The guide also allows an enum glob inside the function that is primarily dealing with that enum. The checker cannot tell an enum from any other glob, so mark that line:

```rust
use Opcode::*; // pasta:ignore rust_glob_import (enum variants inside this function)
```

Put the reason after `(` so it is not read as another rule name.

## Also follow, not checked

- Import a trait in the function that uses it, unless the trait is used throughout the file.
- Prefer `expect` with a reason over `unwrap` in production code. Tests may use `unwrap`.
- Prefer pattern matching over check-then-unwrap.
- An `unsafe` block has a `// SAFETY:` comment that states the invariant.
- Prefer borrows over copies. Reach for `Rc` and `Arc` only when shared ownership is the actual model.
- Name a getter `foo`, `foo_mut`, `take_foo`, or `set_foo` as the guide describes. Do not prefix a getter with `get_`.
- Accept `impl AsRef<str>` or a slice when the function does not need an owned value.
- Do not call items marked `#[doc(hidden)]` in a crate you do not own.
