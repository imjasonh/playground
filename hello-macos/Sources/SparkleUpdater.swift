import Sparkle
import SwiftUI

/// Owns the Sparkle updater controller for the app lifetime. Created once so
/// background update checks and the Check for Updates menu share one instance.
@MainActor
final class SparkleUpdater: ObservableObject {
    private let controller: SPUStandardUpdaterController

    init() {
        controller = SPUStandardUpdaterController(
            startingUpdater: true,
            updaterDelegate: nil,
            userDriverDelegate: nil
        )
    }

    func checkForUpdates() {
        controller.checkForUpdates(nil)
    }
}
