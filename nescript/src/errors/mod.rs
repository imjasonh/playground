mod diagnostic;
mod render;

pub use diagnostic::{Diagnostic, ErrorCode, Label, Level};
pub use render::render_diagnostics;
