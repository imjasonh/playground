#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // The full compilation pipeline must never panic — errors are reported
    // via diagnostics, not panics.
    if let Ok(source) = std::str::from_utf8(data) {
        let (program, parse_diags) = nescript::parser::parse(source);
        if parse_diags.iter().any(|d| d.is_error()) {
            return;
        }
        let Some(program) = program else { return };

        let analysis = nescript::analyzer::analyze(&program);
        if analysis.diagnostics.iter().any(|d| d.is_error()) {
            return;
        }

        // IR lowering + optimization
        let mut ir = nescript::ir::lower(&program, &analysis);
        nescript::optimizer::optimize(&mut ir);

        // Codegen + assembly
        let codegen =
            nescript::codegen::CodeGen::new(&analysis.var_allocations, &program.constants);
        let instructions = codegen.generate(&program);

        // Linking
        let linker = nescript::linker::Linker::new(program.game.mirroring);
        let _rom = linker.link(&instructions);
    }
});
