import SwiftUI

struct DiagnosticResultView: View {
    let report: DiagnosticReport

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 12) {
                Text(report.body)
                    .font(.body.monospaced())
                    .textSelection(.enabled)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .accessibilityIdentifier("report-body")

                if !report.proposedFixes.isEmpty {
                    Divider()
                    Text("Proposed fixes (not applied)")
                        .font(.headline)
                    ForEach(Array(report.proposedFixes.enumerated()), id: \.offset) { index, fix in
                        Text("\(index + 1). \(fix)")
                            .frame(maxWidth: .infinity, alignment: .leading)
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
