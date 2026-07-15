import Foundation

/// Immutable text report from a diagnostic check — shared by the Manual Toolbox
/// UI and (later) Foundation Models tools.
struct DiagnosticReport: Equatable, Sendable {
    var title: String
    var body: String
    var proposedFixes: [String]

    var markdown: String {
        var lines = ["## \(title)", "", body]
        if !proposedFixes.isEmpty {
            lines.append("")
            lines.append("### Proposed fixes (not applied)")
            for (i, fix) in proposedFixes.enumerated() {
                lines.append("\(i + 1). \(fix)")
            }
        }
        return lines.joined(separator: "\n")
    }
}
