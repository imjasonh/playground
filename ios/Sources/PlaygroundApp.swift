import SwiftUI

/// Entry point for the single "Playground" iOS app. The app itself is just a
/// shell: it shows a launcher (`RootView`) listing every experiment registered
/// in `ExperimentCatalog`. New functional experiments are added there, not as
/// separate apps.
@main
struct PlaygroundApp: App {
    var body: some Scene {
        WindowGroup {
            RootView()
        }
    }
}
