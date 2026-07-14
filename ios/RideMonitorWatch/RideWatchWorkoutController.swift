import Foundation
import HealthKit

/// Keeps the Watch app frontmost and running for the duration of a phone-driven
/// ride by owning an `HKWorkoutSession`. Without a session, watchOS suspends
/// the companion as soon as the wrist drops — so the user would have to open
/// Ride Monitor again mid-ride. Recording still happens on the phone; this
/// session is for Watch runtime only and is discarded (not saved to Health).
@MainActor
final class RideWatchWorkoutController: NSObject, ObservableObject {
    static let shared = RideWatchWorkoutController()

    @Published private(set) var isSessionActive = false
    @Published private(set) var lastErrorMessage: String?

    private let healthStore = HKHealthStore()
    private var session: HKWorkoutSession?
    private var builder: HKLiveWorkoutBuilder?
    /// True once we've asked for HealthKit write access this process.
    private var didRequestAuthorization = false

    private override init() {
        super.init()
    }

    /// Start (or keep) a cycling workout session while a ride is active.
    func sync(isRiding: Bool, startedAt: Date) {
        if isRiding {
            startIfNeeded(startedAt: startedAt)
        } else {
            endIfNeeded()
        }
    }

    /// Invoked when the phone calls `HKHealthStore.startWatchApp` — prefer this
    /// configuration (system-launched) over inventing one locally.
    func handle(_ configuration: HKWorkoutConfiguration) {
        startIfNeeded(startedAt: Date(), configuration: configuration)
    }

    private func startIfNeeded(startedAt: Date, configuration: HKWorkoutConfiguration? = nil) {
        if let session, session.state == .running || session.state == .prepared {
            isSessionActive = true
            return
        }

        Task {
            let authorized = await ensureAuthorization()
            guard authorized else {
                lastErrorMessage = "Health access is required to keep Ride Monitor on-wrist during a ride."
                return
            }
            // Re-check after the await — another path may have started us.
            if let session, session.state == .running || session.state == .prepared {
                isSessionActive = true
                return
            }
            do {
                try beginSession(startedAt: startedAt, configuration: configuration ?? Self.cyclingConfiguration())
            } catch {
                lastErrorMessage = error.localizedDescription
            }
        }
    }

    private func beginSession(startedAt: Date, configuration: HKWorkoutConfiguration) throws {
        // Tear down any leftover session synchronously before starting a new
        // one so an async discard callback can't clear the replacement.
        abandonCurrentSession(discardBuilder: true)

        let session = try HKWorkoutSession(healthStore: healthStore, configuration: configuration)
        let builder = session.associatedWorkoutBuilder()
        builder.dataSource = HKLiveWorkoutDataSource(
            healthStore: healthStore,
            workoutConfiguration: configuration
        )
        session.delegate = self
        builder.delegate = self

        self.session = session
        self.builder = builder

        session.startActivity(with: startedAt)
        builder.beginCollection(withStart: startedAt) { [weak self] success, error in
            Task { @MainActor in
                guard let self, self.session === session else { return }
                if let error {
                    self.lastErrorMessage = error.localizedDescription
                }
                self.isSessionActive = success
            }
        }
        isSessionActive = true
        lastErrorMessage = nil
    }

    private func endIfNeeded() {
        guard session != nil else {
            isSessionActive = false
            return
        }
        abandonCurrentSession(discardBuilder: true)
    }

    /// Stop the current session and drop references. Optionally discard the
    /// HealthKit workout so we don't write a phone-mirrored stub into Health.
    private func abandonCurrentSession(discardBuilder: Bool) {
        let endingSession = session
        let endingBuilder = builder
        session = nil
        builder = nil
        isSessionActive = false

        guard let endingSession else { return }

        let end = Date()
        switch endingSession.state {
        case .running, .paused:
            endingSession.stopActivity(with: end)
            endingSession.end()
        case .prepared:
            endingSession.end()
        default:
            break
        }

        guard discardBuilder, let endingBuilder else { return }
        endingBuilder.endCollection(withEnd: end) { _, _ in
            endingBuilder.discardWorkout()
        }
    }

    private func ensureAuthorization() async -> Bool {
        guard HKHealthStore.isHealthDataAvailable() else { return false }
        let workout = HKObjectType.workoutType()
        switch healthStore.authorizationStatus(for: workout) {
        case .sharingAuthorized:
            return true
        case .sharingDenied:
            return false
        case .notDetermined:
            break
        @unknown default:
            break
        }
        didRequestAuthorization = true
        do {
            try await healthStore.requestAuthorization(toShare: [workout], read: [])
            // Write auth is visible; treat anything but an explicit denial as OK
            // so a successful prompt can proceed into session start.
            return healthStore.authorizationStatus(for: workout) != .sharingDenied
        } catch {
            lastErrorMessage = error.localizedDescription
            return false
        }
    }

    static func cyclingConfiguration() -> HKWorkoutConfiguration {
        let configuration = HKWorkoutConfiguration()
        configuration.activityType = .cycling
        configuration.locationType = .outdoor
        return configuration
    }
}

extension RideWatchWorkoutController: HKWorkoutSessionDelegate {
    nonisolated func workoutSession(
        _ workoutSession: HKWorkoutSession,
        didChangeTo toState: HKWorkoutSessionState,
        from fromState: HKWorkoutSessionState,
        date: Date
    ) {
        Task { @MainActor in
            guard self.session === workoutSession else { return }
            self.isSessionActive = (toState == .running || toState == .paused)
            if toState == .ended || toState == .stopped {
                self.session = nil
                self.builder = nil
                self.isSessionActive = false
            }
        }
    }

    nonisolated func workoutSession(_ workoutSession: HKWorkoutSession, didFailWithError error: Error) {
        Task { @MainActor in
            guard self.session === workoutSession else { return }
            self.lastErrorMessage = error.localizedDescription
            self.session = nil
            self.builder = nil
            self.isSessionActive = false
        }
    }
}

extension RideWatchWorkoutController: HKLiveWorkoutBuilderDelegate {
    nonisolated func workoutBuilderDidCollectEvent(_ workoutBuilder: HKLiveWorkoutBuilder) {}

    nonisolated func workoutBuilder(
        _ workoutBuilder: HKLiveWorkoutBuilder,
        didCollectDataOf collectedTypes: Set<HKSampleType>
    ) {}
}
