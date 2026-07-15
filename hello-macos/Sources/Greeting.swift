import Foundation

/// Tiny pure helper so the Hello Mac app has something unit-testable without a
/// window or AppKit session. Keeps the scaffold honest: CI can prove the
/// macOS app type works before Sparkle / notarization land.
struct Greeting: Equatable, Sendable {
    var name: String

    init(name: String = "Mac") {
        let trimmed = name.trimmingCharacters(in: .whitespacesAndNewlines)
        self.name = trimmed.isEmpty ? "Mac" : trimmed
    }

    var text: String {
        "Hello, \(name)!"
    }
}
