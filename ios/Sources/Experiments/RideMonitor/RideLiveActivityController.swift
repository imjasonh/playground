import Foundation
import ActivityKit

/// Starts, updates, and ends the Ride Monitor Live Activity while a ride is
/// in progress. No-ops when Live Activities are unavailable or disabled.
@MainActor
final class RideLiveActivityController {
    static let shared = RideLiveActivityController()

    private var activity: Activity<RideMonitorAttributes>?

    private init() {}

    func start(startedAt: Date, snapshot: RideLiveSnapshot) {
        guard ActivityAuthorizationInfo().areActivitiesEnabled else { return }

        // End any stale activities left over from a previous launch.
        for existing in Activity<RideMonitorAttributes>.activities {
            Task { await existing.end(nil, dismissalPolicy: .immediate) }
        }

        let attributes = RideMonitorAttributes(startedAt: startedAt)
        let state = RideMonitorAttributes.ContentState(snapshot: snapshot)
        do {
            let content = ActivityContent(state: state, staleDate: nil)
            activity = try Activity.request(attributes: attributes, content: content, pushType: nil)
        } catch {
            activity = nil
        }
    }

    func update(snapshot: RideLiveSnapshot) {
        guard let activity else { return }
        let state = RideMonitorAttributes.ContentState(snapshot: snapshot)
        let content = ActivityContent(state: state, staleDate: nil)
        Task { await activity.update(content) }
    }

    func end(snapshot: RideLiveSnapshot?) {
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
}
