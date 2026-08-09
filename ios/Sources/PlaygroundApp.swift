import SwiftUI

/// Entry point for the single "Playground" iOS app. The app itself is just a
/// shell: it shows a launcher (`RootView`) listing every experiment registered
/// in `ExperimentCatalog`. New functional experiments are added there, not as
/// separate apps.
@main
struct PlaygroundApp: App {
    init() {
        // BGTaskScheduler refuses registrations once launch is finished, and
        // the penalty is a crash at the next submit rather than an error here
        // — so Wasm Service's background window is claimed before any view
        // exists. Touching the model at the same time is deliberate: the
        // window's job is to bring a cached module back up, and the handler
        // reaches it through a closure the model installs when it is created.
        WasmServiceBackground.shared.registerLaunchHandler()
        _ = WasmServiceModel.shared
    }

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
