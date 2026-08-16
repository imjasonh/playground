import SwiftUI

struct DiagnosticResultView: View {
    let report: DiagnosticReport

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 12) {
                HStack {
                    Spacer(minLength: 0)
                    Button("Copy body") {
                        PasteboardCopy.string(report.body)
                    }
                    .controlSize(.small)
                    Button("Copy report") {
                        PasteboardCopy.string(report.markdown)
                    }
                    .controlSize(.small)
                    .accessibilityIdentifier("copy-report-inline")
                }

                Text(report.body)
                    .font(.body.monospaced())
                    .textSelection(.enabled)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .accessibilityIdentifier("report-body")

                if !report.actionableFixes.isEmpty {
                    Divider()
                    HStack {
                        Text("Proposed fixes (not applied)")
                            .font(.headline)
                        Spacer()
                        Button("Copy fixes") {
                            let text = report.actionableFixes.enumerated()
                                .map { "\($0.offset + 1). \($0.element)" }
                                .joined(separator: "\n")
                            PasteboardCopy.string(text)
                        }
                        .controlSize(.small)
                        .accessibilityIdentifier("copy-fixes")
                    }
                    ForEach(Array(report.actionableFixes.enumerated()), id: \.offset) { index, fix in
                        HStack(alignment: .top, spacing: 8) {
                            Text("\(index + 1).")
                                .foregroundStyle(.secondary)
                            MarkdownText(source: fix, font: .body)
                            Button {
                                PasteboardCopy.string(fix)
                            } label: {
                                Image(systemName: "doc.on.doc")
                                    .font(.caption)
                            }
                            .buttonStyle(.plain)
                            .help("Copy this fix")
                        }
                    }
                    .accessibilityIdentifier("proposed-fixes")
                }
            }
            .padding(12)
            .frame(maxWidth: .infinity, alignment: .leading)
            .background(Color.primary.opacity(0.04))
            .clipShape(RoundedRectangle(cornerRadius: 8))
        }
    }
}
