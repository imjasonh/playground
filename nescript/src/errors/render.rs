use super::Diagnostic;
use super::Level;

/// Render diagnostics to stderr using ariadne for beautiful error output.
pub fn render_diagnostics(source: &str, filename: &str, diagnostics: &[Diagnostic]) {
    use ariadne::{Color, Label, Report, ReportKind, Source};

    for diag in diagnostics {
        let kind = match diag.level {
            Level::Error => ReportKind::Error,
            Level::Warning => ReportKind::Warning,
        };

        let mut report = Report::build(kind, filename, diag.span.start as usize)
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
            .eprint((filename, Source::from(source)))
            .ok();
    }
}
