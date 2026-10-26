mod inline_parser;
mod opcodes;
#[cfg(test)]
mod tests;

pub use inline_parser::parse_inline;
pub use opcodes::{AddressingMode, Instruction, Opcode};

use std::collections::HashMap;

/// Assemble a list of instructions into bytes, resolving labels.
pub fn assemble(instructions: &[Instruction], base_address: u16) -> AssembleResult {
    let mut assembler = Assembler::new(base_address);
    assembler.assemble(instructions)
}

/// Assemble like [`assemble`], but seed the assembler's label table
/// with externally-resolved labels first. Labels passed in are visible
/// to fixups in this assembly pass even though they're never defined
/// inside `instructions` — useful for cross-bank linking, where the
/// fixed bank's `JSR __ir_fn_foo` needs to resolve a label that lives
/// in a separately-assembled switchable bank.
///
/// Definitions inside `instructions` shadow any seeded label of the
/// same name. The returned `labels` map contains both the seeded
/// entries and any labels defined in this pass — callers can use it
/// as the merged symbol table for symbol-file emission.
pub fn assemble_with_labels<S: std::hash::BuildHasher>(
    instructions: &[Instruction],
    base_address: u16,
    seed_labels: &HashMap<String, u16, S>,
) -> AssembleResult {
    let mut assembler = Assembler::new(base_address);
    for (name, addr) in seed_labels {
        assembler.labels.insert(name.clone(), *addr);
    }
    assembler.assemble(instructions)
}

/// Discovery-only assembly pass for cross-bank linking. Walks
/// `instructions` once, producing the label table (each label's
/// address inside the `base_address`-aligned window) and the raw
/// byte stream — but **skips fixup resolution entirely**. This lets
/// the linker discover what labels live inside a switchable bank
/// before the fixed bank has been assembled, without panicking on
/// fixups that reference still-unknown fixed-bank labels.
///
/// Use [`assemble_with_labels`] for the final pass once the merged
/// label table is available; the discovery output is throwaway.
pub fn assemble_discover_labels<S: std::hash::BuildHasher>(
    instructions: &[Instruction],
    base_address: u16,
    seed_labels: &HashMap<String, u16, S>,
) -> AssembleResult {
    let mut assembler = Assembler::new(base_address);
    for (name, addr) in seed_labels {
        assembler.labels.insert(name.clone(), *addr);
    }
    // First pass only — no fixup resolution. We still emit bytes so
    // the per-instruction sizes are correct (label addresses are
    // computed from the running output length), but unresolved
    // label fixups stay as zero-byte placeholders.
    for inst in instructions {
        assembler.emit_instruction(inst);
    }
    AssembleResult {
        bytes: assembler.output.clone(),
        labels: assembler.labels.clone(),
    }
}

/// Assemble a single instruction into bytes (no label resolution).
pub fn assemble_instruction(opcode: Opcode, mode: &AddressingMode) -> Option<Vec<u8>> {
    let op = opcodes::encode(opcode, mode)?;
    let operand = mode.operand_bytes();
    let mut bytes = vec![op];
    bytes.extend_from_slice(&operand);
    Some(bytes)
}

pub struct AssembleResult {
    pub bytes: Vec<u8>,
    pub labels: HashMap<String, u16>,
}

struct Assembler {
    base_address: u16,
    output: Vec<u8>,
    labels: HashMap<String, u16>,
    fixups: Vec<Fixup>,
}

struct Fixup {
    offset: usize,
    label: String,
    kind: FixupKind,
}

enum FixupKind {
    Absolute, // 2-byte absolute address
    Relative, // 1-byte signed offset (branch)
    Lo,       // low byte of address
    Hi,       // high byte of address
}

impl Assembler {
    fn new(base_address: u16) -> Self {
        Self {
            base_address,
            output: Vec::new(),
            labels: HashMap::new(),
            fixups: Vec::new(),
        }
    }

    fn current_address(&self) -> u16 {
        self.base_address.wrapping_add(self.output.len() as u16)
    }

    fn assemble(&mut self, instructions: &[Instruction]) -> AssembleResult {
        // First pass: emit bytes, collect labels, record fixups
        for inst in instructions {
            self.emit_instruction(inst);
        }

        // Second pass: resolve fixups
        self.resolve_fixups();

        AssembleResult {
            bytes: self.output.clone(),
            labels: self.labels.clone(),
        }
    }

    fn emit_instruction(&mut self, inst: &Instruction) {
        match &inst.mode {
            AddressingMode::Bytes(payload) if inst.opcode == Opcode::NOP => {
                // Raw-data pseudo-instruction: splice the payload
                // into the output stream verbatim. No opcode byte
                // is emitted — this is how we embed audio tables
                // and other data blobs inside a code section while
                // still letting the two-pass label resolver see
                // adjacent labels at the right addresses.
                self.output.extend_from_slice(payload);
            }
            AddressingMode::Label(name) => {
                // A `NOP` with a `Label` mode is the label-definition
                // pseudo-instruction: it records the current address and
                // emits no bytes. Any other opcode paired with `Label` is
                // an actual jump-style instruction targeting that label
                // (e.g. `JMP __ir_main_loop`, `JSR __ir_fn_frame`), which
                // needs an opcode byte plus a 2-byte absolute-address
                // fixup resolved in the second pass.
                if inst.opcode == Opcode::NOP {
                    self.labels.insert(name.clone(), self.current_address());
                } else if let Some(op) = opcodes::encode(inst.opcode, &AddressingMode::Absolute(0))
                {
                    self.output.push(op);
                    self.fixups.push(Fixup {
                        offset: self.output.len(),
                        label: name.clone(),
                        kind: FixupKind::Absolute,
                    });
                    self.output.push(0); // placeholder low byte
                    self.output.push(0); // placeholder high byte
                } else {
                    panic!(
                        "opcode {:?} cannot target a label (no absolute encoding)",
                        inst.opcode
                    );
                }
            }
            AddressingMode::LabelRelative(name) => {
                // Branch to label — emit opcode + placeholder
                if let Some(op) = opcodes::encode(inst.opcode, &AddressingMode::Relative(0)) {
                    self.output.push(op);
                    self.fixups.push(Fixup {
                        offset: self.output.len(),
                        label: name.clone(),
                        kind: FixupKind::Relative,
                    });
                    self.output.push(0); // placeholder
                }
            }
            AddressingMode::LabelAbsoluteX(name) => {
                // `STA label,X` style indexed store with a label-
                // resolved base address. Encodes like `absolute,X`
                // but the 16-bit address is patched in by the
                // fixup pass, same as plain `Label` fixups.
                if let Some(op) = opcodes::encode(inst.opcode, &AddressingMode::AbsoluteX(0)) {
                    self.output.push(op);
                    self.fixups.push(Fixup {
                        offset: self.output.len(),
                        label: name.clone(),
                        kind: FixupKind::Absolute,
                    });
                    self.output.push(0); // placeholder low byte
                    self.output.push(0); // placeholder high byte
                } else {
                    panic!("opcode {:?} cannot target an absolute,X label", inst.opcode);
                }
            }
            AddressingMode::SymbolLo(name) => {
                if let Some(op) = opcodes::encode(inst.opcode, &AddressingMode::Immediate(0)) {
                    self.output.push(op);
                    self.fixups.push(Fixup {
                        offset: self.output.len(),
                        label: name.clone(),
                        kind: FixupKind::Lo,
                    });
                    self.output.push(0);
                }
            }
            AddressingMode::SymbolHi(name) => {
                if let Some(op) = opcodes::encode(inst.opcode, &AddressingMode::Immediate(0)) {
                    self.output.push(op);
                    self.fixups.push(Fixup {
                        offset: self.output.len(),
                        label: name.clone(),
                        kind: FixupKind::Hi,
                    });
                    self.output.push(0);
                }
            }
            mode => {
                if let Some(op) = opcodes::encode(inst.opcode, mode) {
                    self.output.push(op);
                    self.output.extend_from_slice(&mode.operand_bytes());
                } else if let Some(abs_addr) = mode.as_absolute_address() {
                    // Try encoding as absolute if we had a symbolic form
                    self.fixups.push(Fixup {
                        offset: self.output.len(),
                        label: format!("__abs_{abs_addr:04X}"),
                        kind: FixupKind::Absolute,
                    });
                }
            }
        }
    }

    fn resolve_fixups(&mut self) {
        for fixup in &self.fixups {
            if let Some(&addr) = self.labels.get(&fixup.label) {
                match fixup.kind {
                    FixupKind::Absolute => {
                        let bytes = addr.to_le_bytes();
                        self.output[fixup.offset] = bytes[0];
                        self.output[fixup.offset + 1] = bytes[1];
                    }
                    FixupKind::Relative => {
                        #[allow(clippy::cast_possible_wrap)]
                        let from = i32::from(self.base_address) + fixup.offset as i32 + 1;
                        let to = i32::from(addr);
                        let offset = to - from;
                        assert!(
                            (-128..=127).contains(&offset),
                            "branch offset {offset} out of range (-128..127) for label '{}'",
                            fixup.label
                        );
                        self.output[fixup.offset] = (offset as i8).cast_unsigned();
                    }
                    FixupKind::Lo => {
                        self.output[fixup.offset] = addr as u8;
                    }
                    FixupKind::Hi => {
                        self.output[fixup.offset] = (addr >> 8) as u8;
                    }
                }
            } else {
                panic!("unresolved label: '{}'", fixup.label);
            }
        }
    }
}
