import SwiftUI

/// Entry point for the Hello Mac sample app — the macOS counterpart of the
/// static `hello/` browser demo. Intentionally tiny: proves discovery, CI, and
/// (later) Sparkle release plumbing before real macOS apps land.
@main
struct HelloMacApp: App {
    var body: some Scene {
        WindowGroup {
            ContentView()
        }
        .defaultSize(width: 420, height: 280)
    }
}
