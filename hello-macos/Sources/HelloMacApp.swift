import SwiftUI

/// Entry point for the Hello Mac sample app — the macOS counterpart of the
/// static `hello/` browser demo. Proves discovery, CI, notarized Sparkle CD,
/// and in-app Check for Updates against the gh-pages appcast.
@main
struct HelloMacApp: App {
    @StateObject private var updater = SparkleUpdater()

    var body: some Scene {
        WindowGroup {
            ContentView()
        }
        .defaultSize(width: 420, height: 280)
        .commands {
            CommandGroup(after: .appInfo) {
                Button("Check for Updates…") {
                    updater.checkForUpdates()
                }
            }
        }
    }
}
