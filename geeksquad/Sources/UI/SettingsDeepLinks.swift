import AppKit
import Foundation

/// Deep-links for System Settings panes commonly cited in Geek Squad advice.
enum SettingsDeepLinks {
    struct Pane: Equatable {
        /// Phrases to match in prose (longest match wins). First entry is canonical.
        var phrases: [String]
        var urlString: String

        var url: URL { URL(string: urlString)! }
    }

    /// Prefer longer / more specific paths first when linkifying.
    static let panes: [Pane] = [
        Pane(
            phrases: [
                "System Settings → General → Login Items & Extensions",
                "System Settings -> General -> Login Items & Extensions",
                "Login Items & Extensions",
            ],
            urlString: "x-apple.systempreferences:com.apple.LoginItems-Settings.extension"
        ),
        Pane(
            phrases: [
                "App background items",
                "Allow in the Background",
            ],
            urlString: "x-apple.systempreferences:com.apple.LoginItems-Settings.extension?BackgroundItems"
        ),
        Pane(
            phrases: [
                "System Settings → General → Storage",
                "System Settings -> General -> Storage",
            ],
            urlString: "x-apple.systempreferences:com.apple.settings.Storage"
        ),
        Pane(
            phrases: [
                "System Settings → Network → Details → DNS",
                "System Settings -> Network -> Details -> DNS",
                "System Settings → Network → DNS",
                "System Settings -> Network -> DNS",
            ],
            urlString: "x-apple.systempreferences:com.apple.Network-Settings.extension?DNS"
        ),
        Pane(
            phrases: [
                "System Settings → Network → Details → Proxies",
                "System Settings -> Network -> Details -> Proxies",
                "System Settings → Network → Proxies",
                "System Settings -> Network -> Proxies",
            ],
            urlString: "x-apple.systempreferences:com.apple.Network-Settings.extension?Proxies"
        ),
        Pane(
            phrases: [
                "System Settings → Network",
                "System Settings -> Network",
            ],
            urlString: "x-apple.systempreferences:com.apple.Network-Settings.extension"
        ),
        Pane(
            phrases: [
                "System Settings → Battery",
                "System Settings -> Battery",
            ],
            urlString: "x-apple.systempreferences:com.apple.Battery-Settings.extension"
        ),
        Pane(
            phrases: [
                "System Settings → Siri & Spotlight",
                "System Settings -> Siri & Spotlight",
                "System Settings → Spotlight",
                "System Settings -> Spotlight",
            ],
            urlString: "x-apple.systempreferences:com.apple.Spotlight-Settings.extension"
        ),
        Pane(
            phrases: [
                "System Settings → Privacy & Security",
                "System Settings -> Privacy & Security",
            ],
            urlString: "x-apple.systempreferences:com.apple.settings.PrivacySecurity.extension"
        ),
        Pane(
            phrases: [
                "Apple Intelligence & Siri",
                "System Settings → Apple Intelligence & Siri",
                "System Settings -> Apple Intelligence & Siri",
            ],
            urlString: "x-apple.systempreferences:com.apple.Siri-Settings.extension"
        ),
    ]

    static func linkify(_ source: String) -> String {
        let phrases = panes
            .flatMap { pane in pane.phrases.map { ($0, pane.urlString) } }
            .sorted { $0.0.count > $1.0.count }

        var output = source
        for (phrase, urlString) in phrases {
            output = replaceUnlinked(phrase: phrase, withMarkdownLinkTo: urlString, in: output)
        }
        return output
    }

    @discardableResult
    static func open(_ url: URL) -> Bool {
        guard url.scheme == "x-apple.systempreferences" else { return false }
        return NSWorkspace.shared.open(url)
    }

    /// Replace bare phrase occurrences that are not already markdown links.
    private static func replaceUnlinked(
        phrase: String,
        withMarkdownLinkTo urlString: String,
        in source: String
    ) -> String {
        var output = ""
        var search = source[...]
        while let range = search.range(of: phrase) {
            let before = search[..<range.lowerBound]
            let after = search[range.upperBound...]
            output += before
            let alreadyLinked = before.last == "[" && after.hasPrefix("](")
            if alreadyLinked {
                output += phrase
            } else {
                output += "[\(phrase)](\(urlString))"
            }
            search = after
        }
        output += search
        return output
    }
}
