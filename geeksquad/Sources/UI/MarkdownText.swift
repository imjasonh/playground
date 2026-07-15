import SwiftUI

/// Renders model output as Markdown when possible; falls back to plain text.
struct MarkdownText: View {
    let source: String
    var font: Font = .body
    var monospaced: Bool = false

    var body: some View {
        Text(attributed)
            .font(monospaced ? .body.monospaced() : font)
            .textSelection(.enabled)
            .frame(maxWidth: .infinity, alignment: .leading)
            .fixedSize(horizontal: false, vertical: true)
    }

    private var attributed: AttributedString {
        let options = AttributedString.MarkdownParsingOptions(
            interpretedSyntax: .inlineOnlyPreservingWhitespace
        )
        if let parsed = try? AttributedString(
            markdown: source,
            options: options
        ) {
            return parsed
        }
        // Full markdown (headings/lists) — second try without inline-only.
        if let parsed = try? AttributedString(markdown: source) {
            return parsed
        }
        return AttributedString(source)
    }
}
