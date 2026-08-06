import Foundation

/// Decisions that keep the Ride Monitor Watch companion frontmost during a
/// phone-driven ride.
///
/// watchOS only returns a third-party app on wrist-raise while an
/// `HKWorkoutSession` is active — and even then, pressing the Digital Crown
/// dismisses the app until something brings it forward again. The phone
/// periodically re-calls `startWatchApp`, and the Watch restarts a lost
/// session, using these intervals / caps.
enum RideWatchFrontmostPolicy {
    /// How often the phone may re-assert the Watch companion while riding.
    /// Short enough to recover from an accidental Crown press mid-ride;
    /// long enough to avoid spamming HealthKit.
    static let relaunchInterval: TimeInterval = 45

    /// Cap unexpected Watch-side session restarts so a competing workout
    /// (or denied Health access) cannot loop forever.
    static let maxUnexpectedRestarts = 8

    /// Whether the phone should call `HKHealthStore.startWatchApp` now.
    static func shouldLaunchWatch(
        didLaunchThisRide: Bool,
        lastLaunchAt: Date?,
        now: Date,
        interval: TimeInterval = relaunchInterval
    ) -> Bool {
        if !didLaunchThisRide { return true }
        guard let lastLaunchAt else { return true }
        return now.timeIntervalSince(lastLaunchAt) >= interval
    }

    /// Whether the Watch should try to start a new session after an
    /// unexpected end/failure while the phone ride is still active.
    static func shouldRestartAfterUnexpectedEnd(
        wantsSession: Bool,
        failureCount: Int,
        maxFailures: Int = maxUnexpectedRestarts
    ) -> Bool {
        wantsSession && failureCount < maxFailures
    }

    /// Backoff before an unexpected Watch session restart.
    static func restartDelay(afterFailureCount failures: Int) -> TimeInterval {
        let clamped = max(0, min(failures, 5))
        return pow(2.0, Double(clamped)) // 1, 2, 4, 8, 16, 32
    }
}
