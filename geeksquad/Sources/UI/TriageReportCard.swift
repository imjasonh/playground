import SwiftUI

struct TriageReportCard: View {
    let report: TriageReportViewModel

    var body: some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack(alignment: .firstTextBaseline) {
                Text(report.headline)
                    .font(.headline)
                    .fixedSize(horizontal: false, vertical: true)
                Spacer(minLength: 8)
                Button {
                    PasteboardCopy.string(report.markdown)
                } label: {
                    Image(systemName: "doc.on.doc")
                }
                .buttonStyle(.plain)
                .help("Copy report")
                .accessibilityIdentifier("copy-triage-report")
            }

            labeled("Likely cause", report.likelyCause)

            if !report.evidence.isEmpty {
                Text("Evidence")
                    .font(.subheadline.weight(.semibold))
                ForEach(Array(report.evidence.enumerated()), id: \.offset) { _, item in
                    HStack(alignment: .top, spacing: 4) {
                        Text("•")
                        MarkdownText(source: item, font: .body)
                    }
                }
            }

            if !report.proposedSteps.isEmpty {
                HStack {
                    Text("Proposed steps (not applied)")
                        .font(.subheadline.weight(.semibold))
                    Spacer()
                    Button("Copy steps") {
                        let text = report.proposedSteps.enumerated()
                            .map { "\($0.offset + 1). \($0.element)" }
                            .joined(separator: "\n")
                        PasteboardCopy.string(text)
                    }
                    .controlSize(.small)
                }
                ForEach(Array(report.proposedSteps.enumerated()), id: \.offset) { index, step in
                    HStack(alignment: .top, spacing: 8) {
                        Text("\(index + 1).")
                            .foregroundStyle(.secondary)
                        MarkdownText(source: step, font: .body)
                        Button {
                            PasteboardCopy.string(step)
                        } label: {
                            Image(systemName: "doc.on.doc")
                                .font(.caption)
                        }
                        .buttonStyle(.plain)
                    }
                }
            }
        }
        .padding(12)
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(Color.accentColor.opacity(0.08))
        .clipShape(RoundedRectangle(cornerRadius: 10))
        .accessibilityIdentifier("triage-report-card")
    }

    private func labeled(_ title: String, _ body: String) -> some View {
        VStack(alignment: .leading, spacing: 2) {
            Text(title)
                .font(.subheadline.weight(.semibold))
            MarkdownText(source: body, font: .body)
        }
    }
}
