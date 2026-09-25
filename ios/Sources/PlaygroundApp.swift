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
                // Ride Monitor Live Activities can outlive a force-quit. Clear
                // orphans at cold launch so Dynamic Island / Lock Screen don't
                // keep looking like a ride is recording before the user opens
                // the experiment.
                .onAppear {
                    RideLiveActivityController.shared.endOrphansIfNeeded()
                }
        }
    }
}
