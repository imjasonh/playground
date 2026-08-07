import Foundation

/// Pure decisions for Ride Monitor Live Activity lifecycle.
///
/// Kept free of ActivityKit so unit tests (and the Watch target) can cover the
/// rules without a Live Activity runtime.
enum RideLiveActivityPolicy {
    /// How long the finished-ride Live Activity stays on Lock Screen / Dynamic
    /// Island as a summary before the system auto-dismisses it.
    static let summaryRetention: TimeInterval = 30 * 60

    /// End system-presented leftovers only when this process is not mid-ride.
    ///
    /// After a force-quit or crash, `Activity.activities` can still list a Live
    /// Activity while our in-memory handle is gone. Clearing those when idle
    /// stops the Lock Screen / Dynamic Island from looking like an active ride.
    /// Intentionally ended summaries use `.after(summaryRetention)` and are
    /// already removed from `Activity.activities`, so this sweep does not cut
    /// their ~30 minute retention short.
    static func shouldEndOrphans(hasTrackedActivity: Bool, hasPendingStart: Bool) -> Bool {
        !hasTrackedActivity && !hasPendingStart
    }

    /// Wall-clock deadline passed to `ActivityUIDismissalPolicy.after(_:)`.
    static func summaryDismissalDate(from endDate: Date = Date()) -> Date {
        endDate.addingTimeInterval(summaryRetention)
    }

    /// Closed timer interval for an ended ride so `Text(timerInterval:)` cannot
    /// keep ticking past stop (open-ended `...Date.distantFuture` only while
    /// `isRiding` is true).
    static func endedTimerInterval(
        startedAt: Date,
        elapsedSeconds: TimeInterval
    ) -> ClosedRange<Date> {
        let end = startedAt.addingTimeInterval(max(0, elapsedSeconds))
        if end < startedAt { return startedAt...startedAt }
        return startedAt...end
    }
}
