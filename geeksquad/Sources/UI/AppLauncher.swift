import AppKit
import Foundation

enum AppLauncher {
    /// Opens a macOS utility/app by name (e.g. "Activity Monitor").
    @discardableResult
    static func openApp(named name: String) -> Bool {
        let trimmed = name.trimmingCharacters(in: .whitespacesAndNewlines)
            .removingPercentEncoding ?? name.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return false }
        let candidates = [
            "/System/Applications/Utilities/\(trimmed).app",
            "/Applications/Utilities/\(trimmed).app",
            "/System/Applications/\(trimmed).app",
            "/Applications/\(trimmed).app",
        ]
        for path in candidates where FileManager.default.fileExists(atPath: path) {
            return NSWorkspace.shared.open(URL(fileURLWithPath: path))
        }
        return NSWorkspace.shared.launchApplication(trimmed)
    }

    /// Handles `geeksquad://open-app/Activity%20Monitor`.
    static func handleGeekSquadURL(_ url: URL) -> Bool {
        guard url.scheme == "geeksquad" else { return false }
        if url.host == "open-app" {
            let name = url.path.trimmingCharacters(in: CharacterSet(charactersIn: "/"))
            return openApp(named: name)
        }
        let parts = url.pathComponents.filter { $0 != "/" }
        if parts.first == "open-app", parts.count >= 2 {
            return openApp(named: parts.dropFirst().joined(separator: " "))
        }
        return false
    }
}

/// Turns bare “Activity Monitor” mentions into tappable markdown links.
enum ActivityMonitorLinks {
    static let markdownURL = "geeksquad://open-app/Activity%20Monitor"
    static let phrase = "Activity Monitor"

    static func linkify(_ source: String) -> String {
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
                output += "[\(phrase)](\(markdownURL))"
            }
            search = after
        }
        output += search
        return output
    }
}
