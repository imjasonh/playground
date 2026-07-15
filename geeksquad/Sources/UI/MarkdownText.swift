import SwiftUI

/// Renders model output as Markdown when possible; falls back to plain text.
/// Bare “Activity Monitor” mentions become tappable links that open the app.
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
            .environment(\.openURL, OpenURLAction { url in
                if AppLauncher.handleGeekSquadURL(url) {
                    return .handled
                }
                return .systemAction
            })
    }

    private var attributed: AttributedString {
        let linked = ActivityMonitorLinks.linkify(source)
        // Prefer full Markdown so **bold**, lists, and headings render.
        if let parsed = try? AttributedString(markdown: linked) {
            return parsed
        }
        let options = AttributedString.MarkdownParsingOptions(
            interpretedSyntax: .inlineOnlyPreservingWhitespace
        )
        if let parsed = try? AttributedString(markdown: linked, options: options) {
            return parsed
        }
        return AttributedString(linked)
    }
}
