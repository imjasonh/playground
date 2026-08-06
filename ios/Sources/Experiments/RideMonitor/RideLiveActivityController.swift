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
    /// Bumps so an in-flight async start/update is abandoned if a newer
    /// start/end wins.
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

    /// Call when the host app becomes active so a deferred start can proceed,
    /// or so force-quit leftovers can be cleared while idle.
    func handleSceneBecameActive() {
        endOrphansIfNeeded()
        guard pendingStart != nil, activity == nil else { return }
        #if canImport(UIKit)
        guard UIApplication.shared.applicationState == .active else { return }
        #endif
        enqueueStart()
    }

    /// Ends Live Activities left behind after a crash / force-quit when this
    /// process is not recording. Safe at cold launch and whenever the UI shows
    /// idle (Start ride).
    func endOrphansIfNeeded() {
        let hasTracked = activity != nil
        let hasPending = pendingStart != nil
        guard RideLiveActivityPolicy.shouldEndOrphans(
            hasTrackedActivity: hasTracked,
            hasPendingStart: hasPending
        ) else { return }

        let orphans = Activity<RideMonitorAttributes>.activities
        guard !orphans.isEmpty else { return }

        RideMonitorLog.notice("ending \(orphans.count) orphan Live Activity(ies)")
        generation += 1
        Task {
            for existing in Activity<RideMonitorAttributes>.activities {
                await existing.end(nil, dismissalPolicy: .immediate)
            }
        }
    }

    func update(snapshot: RideLiveSnapshot) {
        // Keep a deferred / in-flight start's content fresh until request lands.
        if activity == nil, var pending = pendingStart {
            pending.snapshot = snapshot
            pendingStart = pending
        }
        guard let activity else { return }
        let token = generation
        let state = RideMonitorAttributes.ContentState(snapshot: snapshot)
        let content = ActivityContent(state: state, staleDate: nil)
        Task {
            // Drop updates that lost a race with `end()` / a newer start.
            guard token == self.generation else { return }
            await activity.update(content)
        }
    }

    func end(snapshot: RideLiveSnapshot?) {
        pendingStart = nil
        generation += 1
        let content: ActivityContent<RideMonitorAttributes.ContentState>? = snapshot.map {
            // Mark final content stale immediately so Lock Screen / Dynamic
            // Island chrome cannot keep looking "live" if dismissal is delayed.
            ActivityContent(
                state: RideMonitorAttributes.ContentState(snapshot: $0),
                staleDate: Date()
            )
        }
        let tracked = activity
        activity = nil

        // Capture the system list now, then sweep again after awaits — a raced
        // `request` or force-quit leftover can otherwise linger.
        let known = Activity<RideMonitorAttributes>.activities
        Task {
            var seen = Set<String>()
            if let tracked {
                seen.insert(tracked.id)
                // Immediate dismissal: `.default` left the activity on Lock
                // Screen / Dynamic Island for hours, which looked like the ride
                // was still recording after Stop.
                await tracked.end(content, dismissalPolicy: .immediate)
            }
            for existing in known where !seen.contains(existing.id) {
                seen.insert(existing.id)
                await existing.end(content, dismissalPolicy: .immediate)
            }
            for existing in Activity<RideMonitorAttributes>.activities where !seen.contains(existing.id) {
                await existing.end(content, dismissalPolicy: .immediate)
            }
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

        // Re-check after awaiting — an interleaved `end()` or newer start must win.
        guard token == generation, let pending = pendingStart, activity == nil else { return }

        let attributes = RideMonitorAttributes(startedAt: pending.startedAt)
        let state = RideMonitorAttributes.ContentState(snapshot: pending.snapshot)
        do {
            let content = ActivityContent(state: state, staleDate: nil)
            // Final generation check immediately before request.
            guard token == generation, pendingStart != nil, activity == nil else { return }
            let requested = try Activity.request(attributes: attributes, content: content, pushType: nil)
            guard token == generation else {
                await requested.end(nil, dismissalPolicy: .immediate)
                return
            }
            activity = requested
            pendingStart = nil
        } catch {
            activity = nil
            // Leave `pendingStart` so a later foreground retry can try again.
            RideMonitorLog.error("Live Activity request failed: \(error.localizedDescription)")
        }
    }
}
