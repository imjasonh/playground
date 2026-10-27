use std::io::Write;

use super::Diagnostic;
use super::Level;

/// Render diagnostics to stderr using ariadne for beautiful error output.
pub fn render_diagnostics(source: &str, filename: &str, diagnostics: &[Diagnostic]) {
    write_diagnostics(source, filename, diagnostics, true, std::io::stderr());
}

/// Render diagnostics to `out`. Spans are byte offsets into `source`, so
/// ariadne must index by byte: its default counts characters, which puts
/// every report after a multi-byte character (a `──` comment rule, `×`)
/// on a later line.
pub fn write_diagnostics<W: Write>(
    source: &str,
    filename: &str,
    diagnostics: &[Diagnostic],
    color: bool,
    mut out: W,
) {
    use ariadne::{Color, Config, IndexType, Label, Report, ReportKind, Source};

    let config = Config::default()
        .with_index_type(IndexType::Byte)
        .with_color(color);

    for diag in diagnostics {
        let kind = match diag.level {
            Level::Error => ReportKind::Error,
            Level::Warning => ReportKind::Warning,
        };

        let mut report = Report::build(kind, filename, diag.span.start as usize)
            .with_config(config)
            .with_code(diag.code.to_string())
            .with_message(&diag.message);

        report = report.with_label(
            Label::new((filename, diag.span.start as usize..diag.span.end as usize))
                .with_color(Color::Red),
        );

        for label in &diag.labels {
            report = report.with_label(
                Label::new((filename, label.span.start as usize..label.span.end as usize))
                    .with_message(&label.message)
                    .with_color(Color::Yellow),
            );
        }

        if let Some(help) = &diag.help {
            report = report.with_help(help);
        }
        if let Some(note) = &diag.note {
            report = report.with_note(note);
        }

        report
            .finish()
            .write((filename, Source::from(source)), &mut out)
            .ok();
    }
}
