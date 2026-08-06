import Foundation

/// Pure decisions for Ride Monitor Live Activity lifecycle.
///
/// Kept free of ActivityKit so unit tests (and the Watch target) can cover the
/// rules without a Live Activity runtime.
enum RideLiveActivityPolicy {
    /// End system-presented leftovers only when this process is not mid-ride.
    ///
    /// After a force-quit or crash, `Activity.activities` can still list a Live
    /// Activity while our in-memory handle is gone. Clearing those when idle
    /// stops the Lock Screen / Dynamic Island from looking like an active ride.
    static func shouldEndOrphans(hasTrackedActivity: Bool, hasPendingStart: Bool) -> Bool {
        !hasTrackedActivity && !hasPendingStart
    }
}
