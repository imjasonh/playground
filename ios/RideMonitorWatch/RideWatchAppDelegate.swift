import Foundation
import WatchKit
import HealthKit

/// Receives `startWatchApp` launches from the phone so we can start the
/// frontmost HealthKit workout session (required for long-running Watch
/// execution — not because the ride is specifically cycling) without the user
/// hunting for the companion.
final class RideWatchAppDelegate: NSObject, WKApplicationDelegate {
    func handle(_ workoutConfiguration: HKWorkoutConfiguration) {
        Task { @MainActor in
            RideWatchWorkoutController.shared.handle(workoutConfiguration)
        }
    }
}
