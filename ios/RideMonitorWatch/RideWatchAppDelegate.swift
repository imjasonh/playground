import Foundation
import WatchKit
import HealthKit

/// Receives `startWatchApp` launches from the phone so we can start the
/// frontmost workout session without the user hunting for the companion.
final class RideWatchAppDelegate: NSObject, WKApplicationDelegate {
    func handle(_ workoutConfiguration: HKWorkoutConfiguration) {
        Task { @MainActor in
            RideWatchWorkoutController.shared.handle(workoutConfiguration)
        }
    }
}
