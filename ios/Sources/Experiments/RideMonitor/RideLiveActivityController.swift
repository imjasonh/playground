import Foundation
import ActivityKit
#if canImport(UIKit)
import UIKit
#endif

/// Starts, updates, and ends the Ride Monitor Live Activity while a ride is
/// in progress. No-ops when Live Activities are unavailable or disabled.
@MainActor
final class RideLiveActivityController {
    static let shared = RideLiveActivityController()

    private var activity: Activity<RideMonitorAttributes>?
    /// Held until `Activity.request` succeeds. Also used to defer starts that
    /// happen while the app is backgrounded (`request` only works when active).
    private var pendingStart: (startedAt: Date, snapshot: RideLiveSnapshot)?
    /// Bumps so an in-flight async start is abandoned if a newer start/end wins.
    private var generation = 0

    private init() {}

    func start(startedAt: Date, snapshot: RideLiveSnapshot) {
        guard ActivityAuthorizationInfo().areActivitiesEnabled else { return }

        pendingStart = (startedAt, snapshot)

        #if canImport(UIKit)
        // Requesting a Live Activity from the background fails silently.
        // Keep `pendingStart` and retry when the scene becomes active again.
        if UIApplication.shared.applicationState != .active {
            return
        }
        #endif

        enqueueStart()
    }

    /// Call when the host app becomes active so a deferred start can proceed.
    func handleSceneBecameActive() {
        guard pendingStart != nil, activity == nil else { return }
        #if canImport(UIKit)
        guard UIApplication.shared.applicationState == .active else { return }
        #endif
        enqueueStart()
    }

    func update(snapshot: RideLiveSnapshot) {
        // Keep a deferred / in-flight start's content fresh until request lands.
        if activity == nil, var pending = pendingStart {
            pending.snapshot = snapshot
            pendingStart = pending
        }
        guard let activity else { return }
        let state = RideMonitorAttributes.ContentState(snapshot: snapshot)
        let content = ActivityContent(state: state, staleDate: nil)
        Task { await activity.update(content) }
    }

    func end(snapshot: RideLiveSnapshot?) {
        pendingStart = nil
        generation += 1
        guard let activity else { return }
        let content: ActivityContent<RideMonitorAttributes.ContentState>? = snapshot.map {
            ActivityContent(state: RideMonitorAttributes.ContentState(snapshot: $0), staleDate: nil)
        }
        let current = activity
        self.activity = nil
        Task {
            await current.end(content, dismissalPolicy: .default)
        }
    }

    private func enqueueStart() {
        generation += 1
        let token = generation
        Task { await self.performStart(token: token) }
    }

    private func performStart(token: Int) async {
        // Await stale ends before requesting so we don't hit the activity limit
        // after a force-quit left a previous ride's Live Activity around.
        let stale = Activity<RideMonitorAttributes>.activities
        for existing in stale {
            await existing.end(nil, dismissalPolicy: .immediate)
        }

        guard token == generation, let pending = pendingStart else { return }

        let attributes = RideMonitorAttributes(startedAt: pending.startedAt)
        let state = RideMonitorAttributes.ContentState(snapshot: pending.snapshot)
        do {
            let content = ActivityContent(state: state, staleDate: nil)
            activity = try Activity.request(attributes: attributes, content: content, pushType: nil)
            pendingStart = nil
        } catch {
            activity = nil
            // Leave `pendingStart` so a later foreground retry can try again.
        }
    }
}
