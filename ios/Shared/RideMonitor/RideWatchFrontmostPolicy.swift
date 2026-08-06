import Foundation

/// Keeps the Ride Monitor Watch companion frontmost for a phone-driven ride.
///
/// Invariant: while the phone ride is active, the Watch must want an
/// `HKWorkoutSession` (watchOS only returns a third-party app on wrist-raise
/// with a live session). Digital Crown dismissal still returns to the clock
/// face even with a session — the phone periodically re-calls `startWatchApp`
/// to bring the UI forward again.
enum RideWatchFrontmostPolicy {
    /// How often the phone may re-assert the Watch UI while riding.
    static let relaunchInterval: TimeInterval = 45

    /// Minimum gap between Watch-side session start attempts.
    static let startAttemptCooldown: TimeInterval = 5

    /// Cap Watch start attempts per ride so permanent HealthKit failures
    /// cannot loop for the whole ride.
    static let maxStartAttemptsPerRide = 8

    /// Phone should call `startWatchApp` when it has never launched this ride
    /// (`lastLaunchAt == nil`) or the relaunch interval has elapsed.
    static func shouldRelaunchWatch(
        lastLaunchAt: Date?,
        now: Date,
        interval: TimeInterval = relaunchInterval
    ) -> Bool {
        guard let lastLaunchAt else { return true }
        return now.timeIntervalSince(lastLaunchAt) >= interval
    }

    /// Watch should attempt to start a session when the phone ride still wants
    /// one, attempts remain, and the cooldown has elapsed.
    static func shouldAttemptStart(
        wantsSession: Bool,
        attemptCount: Int,
        lastAttemptAt: Date?,
        now: Date,
        cooldown: TimeInterval = startAttemptCooldown,
        maxAttempts: Int = maxStartAttemptsPerRide
    ) -> Bool {
        guard wantsSession, attemptCount < maxAttempts else { return false }
        guard let lastAttemptAt else { return true }
        return now.timeIntervalSince(lastAttemptAt) >= cooldown
    }
}
