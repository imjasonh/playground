import AppKit
import Foundation

/// Opens System Settings to the pane where Apple Intelligence can be enabled.
enum AppleIntelligenceSettings {
    /// Apple Intelligence & Siri (macOS Tahoe / 26+). Falls back to Speech on older macOS.
    static let preferenceURLs: [URL] = [
        URL(string: "x-apple.systempreferences:com.apple.Siri-Settings.extension")!,
        URL(string: "x-apple.systempreferences:com.apple.preference.speech")!,
    ]

    @discardableResult
    static func open() -> Bool {
        for url in preferenceURLs where NSWorkspace.shared.open(url) {
            return true
        }
        return false
    }
}
