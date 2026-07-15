import Foundation

/// Immutable text report from a diagnostic check — shared by the Manual Toolbox
/// UI and Foundation Models tools.
struct DiagnosticReport: Equatable, Sendable {
    var title: String
    var body: String
    var proposedFixes: [String]

    var actionableFixes: [String] { RemediationCopy.actionable(proposedFixes) }

    var markdown: String {
        var lines = ["## \(title)", "", body]
        let fixes = actionableFixes
        if !fixes.isEmpty {
            lines.append("")
            lines.append("### Proposed fixes (not applied)")
            for (i, fix) in fixes.enumerated() {
                lines.append("\(i + 1). \(fix)")
            }
        }
        return lines.joined(separator: "\n")
    }

    /// Tool-call returns must stay small — on-device context is ~4k tokens and
    /// tool schemas already consume a large share of it.
    func compactMarkdown(maxCharacters: Int = 1_600) -> String {
        let full = markdown
        guard full.count > maxCharacters else { return full }
        let end = full.index(full.startIndex, offsetBy: maxCharacters)
        return String(full[..<end]) + "\n…(truncated)"
    }
}
