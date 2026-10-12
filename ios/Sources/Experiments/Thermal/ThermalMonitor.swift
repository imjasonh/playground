import Foundation
import ActivityKit

/// Session sample of a thermal-state change, shown on the experiment screen.
struct ThermalSample: Hashable, Identifiable {
    let id: UUID
    let level: ThermalLevel
    let at: Date

    init(id: UUID = UUID(), level: ThermalLevel, at: Date) {
        self.id = id
        self.level = level
        self.at = at
    }
}

/// Observes `ProcessInfo.thermalState` and keeps the Live Activity in sync.
///
/// Starts from the host scene so the island can appear without opening this
/// experiment first. The experiment is the destination for a tap and the
/// place that shows what the level means.
@MainActor
final class ThermalMonitor: ObservableObject {
    static let shared = ThermalMonitor()

    @Published private(set) var level: ThermalLevel
    @Published private(set) var samples: [ThermalSample]
    @Published private(set) var activitiesEnabled: Bool

    private var observer: (any NSObjectProtocol)?
    private var authorizationTask: Task<Void, Never>?

    private init() {
        let current = ThermalLevel(ProcessInfo.processInfo.thermalState)
        level = current
        samples = [ThermalSample(level: current, at: Date())]
        activitiesEnabled = ActivityAuthorizationInfo().areActivitiesEnabled
    }

    func start() {
        if observer == nil {
            observer = NotificationCenter.default.addObserver(
                forName: ProcessInfo.thermalStateDidChangeNotification,
                object: nil,
                queue: .main
            ) { [weak self] _ in
                Task { @MainActor in
                    self?.applyCurrent()
                }
            }
        }
        if authorizationTask == nil {
            authorizationTask = Task { @MainActor [weak self] in
                for await enabled in ActivityAuthorizationInfo().activityEnablementUpdates {
                    guard let self else { return }
                    self.activitiesEnabled = enabled
                    self.applyCurrent()
                }
            }
        }
        applyCurrent()
    }

    func handleSceneBecameActive() {
        activitiesEnabled = ActivityAuthorizationInfo().areActivitiesEnabled
        applyCurrent()
        ThermalLiveActivityController.shared.handleSceneBecameActive()
    }

    private func applyCurrent() {
        let incoming = ThermalLevel(ProcessInfo.processInfo.thermalState)
        if incoming != level {
            level = incoming
            samples.append(ThermalSample(level: incoming, at: Date()))
            let overflow = samples.count - 20
            if overflow > 0 {
                samples.removeFirst(overflow)
            }
        }
        ThermalLiveActivityController.shared.sync(level: incoming)
    }
}
