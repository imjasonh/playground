use super::render::write_diagnostics;
use super::{Diagnostic, ErrorCode};
use crate::lexer::Span;

fn render(source: &str, diag: &Diagnostic) -> String {
    let mut out = Vec::new();
    write_diagnostics(source, "t.ne", std::slice::from_ref(diag), false, &mut out);
    String::from_utf8(out).unwrap()
}

#[test]
fn report_after_multibyte_comment_points_at_the_spanned_line() {
    let source = "// ── ── ── ── ── ── ── ── ── ──\nvar x: u8 = 0\nfun f() {}\n";
    let start = source.find("fun").unwrap() as u32;
    let diag = Diagnostic::warning(ErrorCode::W0103, "w", Span::new(0, start, start + 3));
    let text = render(source, &diag);
    assert!(text.contains("t.ne:3:1"), "{text}");
    assert!(text.contains("3 │ fun f() {}"), "{text}");
}

#[test]
fn analyzer_warning_in_platformer_style_source_names_the_call_line() {
    let source = "game \"W\" { mapper: NROM }\n\
                  // ── ×× → ──────────────────────────────────\n\
                  var x: u8 = 0\n\
                  fun f(a: u8) -> u8 { return a }\n\
                  state Main {\n    on frame {\n        f(x)\n    }\n}\n\
                  start Main\n";
    let (program, parse_diags) = crate::parser::parse(source);
    assert!(parse_diags.iter().all(|d| !d.is_error()), "{parse_diags:?}");
    let analysis = crate::analyzer::analyze(&program.unwrap());
    let drop = analysis
        .diagnostics
        .iter()
        .find(|d| d.code == ErrorCode::W0106)
        .expect("W0106 for the discarded call");
    let text = render(source, drop);
    assert!(text.contains("t.ne:7:9"), "{text}");
    assert!(text.contains("7 │         f(x)"), "{text}");
}

fn analyzer_reports(source: &str) -> Vec<Diagnostic> {
    let (program, parse_diags) = crate::parser::parse(source);
    assert!(parse_diags.iter().all(|d| !d.is_error()), "{parse_diags:?}");
    crate::analyzer::analyze(&program.unwrap()).diagnostics
}

#[test]
fn duplicate_declaration_report_shows_the_declaration_line() {
    let source = "game \"D\" { mapper: NROM }\n\
                  var t: u8 = 0\n\
                  var t: u8 = 1\n\
                  state Main {\n    on frame { t = 2 }\n}\n\
                  start Main\n";
    let dup = analyzer_reports(source)
        .into_iter()
        .find(|d| d.code == ErrorCode::E0501)
        .expect("E0501 for the second `var t`");
    assert_eq!(
        &source[dup.span.start as usize..dup.span.end as usize],
        "var t: u8 = 1"
    );
    let text = render(source, &dup);
    assert!(text.contains("3 │ var t: u8 = 1"), "{text}");
}

#[test]
fn report_on_a_whole_state_shows_its_first_line() {
    let source = "game \"U\" { mapper: NROM }\n\
                  state Main {\n    on frame { }\n}\n\
                  state Lost {\n    on frame { }\n}\n\
                  start Main\n";
    let lost = analyzer_reports(source)
        .into_iter()
        .find(|d| d.code == ErrorCode::W0104)
        .expect("W0104 for the unreachable state");
    let text = render(source, &lost);
    assert!(text.contains("5 │ state Lost {"), "{text}");
}
