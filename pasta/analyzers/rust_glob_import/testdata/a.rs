use ast::*; // want "glob import"

use crate::parser::ast::*; // want "glob import"

use crate::asm::{AddressingMode, Opcode::*}; // want "glob import"

use super::*;

use wasm_bindgen::prelude::*;

pub use submodule::*;

pub(crate) use other::*;

fn encode() {
    use Opcode::*; // want "glob import"
}
