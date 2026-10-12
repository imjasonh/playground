import Foundation
import ActivityKit
import UIKit

/// Starts, updates, and ends the thermal Live Activity. No-ops when Live
/// Activities are unavailable or the incoming state is nominal.
///
/// Requests never include an alert configuration. The island is the intended
/// presentation. iOS still requires a Lock Screen view, which stays one line.
@MainActor
final class ThermalLiveActivityController {
    static let shared = ThermalLiveActivityController()

    private var activity: Activity<ThermalAttributes>?
    /// Held until `Activity.request` succeeds. Also used to defer starts that
    /// happen while the app is backgrounded (`request` only works when active).
    private var pendingLevel: ThermalLevel?
    /// Bumps so an in-flight async start is abandoned if a newer start or end
    /// wins.
    private var generation = 0

    private init() {}

    func handleSceneBecameActive() {
        adoptExistingIfNeeded()
        guard pendingLevel != nil, activity == nil else { return }
        guard UIApplication.shared.applicationState == .active else { return }
        enqueueStart()
    }

    func sync(level: ThermalLevel) {
        adoptExistingIfNeeded()

        let incoming: ThermalLevel
        if ActivityAuthorizationInfo().areActivitiesEnabled {
            incoming = level
        } else {
            incoming = .nominal
        }

        switch ThermalLiveActivityPolicy.action(
            presented: activity?.content.state.level,
            incoming: incoming
        ) {
        case .none:
            return
        case .start(let startLevel):
            pendingLevel = startLevel
            guard UIApplication.shared.applicationState == .active else { return }
            enqueueStart()
        case .update(let updateLevel):
            pendingLevel = nil
            if let activity {
                push(updateLevel, on: activity)
            } else {
                pendingLevel = updateLevel
                guard UIApplication.shared.applicationState == .active else { return }
                enqueueStart()
            }
        case .end:
            pendingLevel = nil
            endAll()
        }
    }

    private func adoptExistingIfNeeded() {
        if activity == nil {
            activity = Activity<ThermalAttributes>.activities.first
        }
    }

    private func enqueueStart() {
        generation += 1
        let token = generation
        Task { await self.performStart(token: token) }
    }

    private func performStart(token: Int) async {
        let stale = Activity<ThermalAttributes>.activities
        for existing in stale {
            await existing.end(nil, dismissalPolicy: .immediate)
        }
        activity = nil

        guard token == generation, let level = pendingLevel, level.showsLiveActivity else { return }
        guard UIApplication.shared.applicationState == .active else { return }

        let state = ThermalAttributes.ContentState(level: level, changedAt: Date())
        let content = ActivityContent(
            state: state,
            staleDate: ThermalLiveActivityPolicy.staleDate()
        )
        do {
            guard token == generation, pendingLevel != nil else { return }
            let requested = try Activity.request(
                attributes: ThermalAttributes(),
                content: content,
                pushType: nil
            )
            guard token == generation else {
                await requested.end(nil, dismissalPolicy: .immediate)
                return
            }
            activity = requested
            pendingLevel = nil
        } catch {
            activity = nil
            ThermalLog.error("Live Activity request failed: \(error.localizedDescription)")
        }
    }

    private func push(_ level: ThermalLevel, on activity: Activity<ThermalAttributes>) {
        let token = generation
        let activityID = activity.id
        let content = ActivityContent(
            state: ThermalAttributes.ContentState(level: level, changedAt: Date()),
            staleDate: ThermalLiveActivityPolicy.staleDate()
        )
        Task {
            guard token == self.generation, self.activity?.id == activityID else { return }
            await activity.update(content)
        }
    }

    private func endAll() {
        generation += 1
        let tracked = activity
        activity = nil
        let known = Activity<ThermalAttributes>.activities
        Task {
            var seen = Set<String>()
            if let tracked {
                seen.insert(tracked.id)
                await tracked.end(nil, dismissalPolicy: .immediate)
            }
            for existing in known where !seen.contains(existing.id) {
                seen.insert(existing.id)
                await existing.end(nil, dismissalPolicy: .immediate)
            }
            for existing in Activity<ThermalAttributes>.activities where !seen.contains(existing.id) {
                await existing.end(nil, dismissalPolicy: .immediate)
            }
        }
    }
}
