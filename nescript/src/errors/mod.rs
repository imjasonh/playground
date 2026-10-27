mod diagnostic;
mod render;
#[cfg(test)]
mod tests;

pub use diagnostic::{Diagnostic, ErrorCode, Label, Level};
pub use render::render_diagnostics;
