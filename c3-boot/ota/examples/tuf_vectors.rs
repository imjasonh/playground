//! Prints one line per TUF case with `c3-verify`'s verdict.
//! `c3-boot-proofs`' `tuf-check` reads the same lines, evaluates the Lean
//! specification, and must print identical lines.
//!
//! A line is `NAME INPUT | VERDICT`. `c3_ota::tuf_cases::Input::describe`
//! defines `INPUT`, and `Input::verdict` defines `VERDICT`.

use std::io::BufWriter;
use std::io::Write as _;

fn main() -> std::io::Result<()> {
    let mut out = BufWriter::new(std::io::stdout().lock());
    for case in c3_ota::tuf_cases::cases() {
        writeln!(
            out,
            "{} {} | {}",
            case.name,
            case.input.describe(),
            case.input.verdict()
        )?;
    }
    out.flush()
}
