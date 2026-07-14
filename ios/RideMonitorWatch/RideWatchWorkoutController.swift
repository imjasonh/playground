import Foundation
import HealthKit
import WatchConnectivity

/// Owns the Watch-side `HKWorkoutSession` that keeps Ride Monitor frontmost
/// during a phone-driven ride, and collects HealthKit activity samples via
/// `HKLiveWorkoutBuilder`.
///
/// Why HealthKit (not "because it's a bike"):
/// watchOS only grants long-running, frontmost execution to apps with an
/// active workout session. `WKExtendedRuntimeSession` is short-lived; a
/// HealthKit workout is the supported way to stay on-wrist for a whole ride.
/// The activity type (`.cycling`) is just context for sensor fusion — any
/// workout type would keep the app active the same way.
///
/// Collected quantities:
/// - Heart rate, active + basal energy (Watch sensors)
/// - Cycling distance (Watch GPS)
/// - Cadence / cycling speed / power when a Bluetooth sensor is paired
///
/// On stop we **finish** the workout into Health and mirror stats back to the
/// phone for the saved ride JSON. GPS track / jolts still record on the phone.
@MainActor
final class RideWatchWorkoutController: NSObject, ObservableObject {
    static let shared = RideWatchWorkoutController()

    @Published private(set) var isSessionActive = false
    @Published private(set) var lastErrorMessage: String?
    @Published private(set) var activity = RideWatchActivityMetrics.empty

    private let healthStore = HKHealthStore()
    private var session: HKWorkoutSession?
    private var builder: HKLiveWorkoutBuilder?
    private var didRequestAuthorization = false
    private var lastMetricsPushAt: TimeInterval = 0
    private let metricsPushInterval: TimeInterval = 1.0

    private override init() {
        super.init()
    }

    /// Start (or keep) a cycling workout session while a ride is active.
    func sync(isRiding: Bool, startedAt: Date) {
        if isRiding {
            startIfNeeded(startedAt: startedAt)
        } else {
            endIfNeeded(saveToHealth: true)
        }
    }

    /// Invoked when the phone calls `HKHealthStore.startWatchApp`.
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
                lastErrorMessage = "Health access is required to keep Ride Monitor on-wrist and collect activity data."
                return
            }
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
        // Drop any leftover session without writing a stub workout.
        endIfNeeded(saveToHealth: false)

        let session = try HKWorkoutSession(healthStore: healthStore, configuration: configuration)
        let builder = session.associatedWorkoutBuilder()
        let dataSource = HKLiveWorkoutDataSource(
            healthStore: healthStore,
            workoutConfiguration: configuration
        )
        for type in Self.collectibleQuantityTypes {
            dataSource.enableCollection(for: type, predicate: nil)
        }
        builder.dataSource = dataSource
        session.delegate = self
        builder.delegate = self

        self.session = session
        self.builder = builder
        activity = .empty

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

    private func endIfNeeded(saveToHealth: Bool) {
        guard session != nil || builder != nil else {
            isSessionActive = false
            if !saveToHealth { activity = .empty }
            return
        }

        let endingSession = session
        let endingBuilder = builder
        session = nil
        builder = nil
        isSessionActive = false

        let end = Date()
        if let endingSession {
            switch endingSession.state {
            case .running, .paused:
                endingSession.stopActivity(with: end)
                endingSession.end()
            case .prepared:
                endingSession.end()
            default:
                break
            }
        }

        guard let endingBuilder else {
            if !saveToHealth { activity = .empty }
            return
        }

        // Publish one last metrics snapshot before finishing / discarding.
        refreshActivity(from: endingBuilder, forcePush: true)

        endingBuilder.endCollection(withEnd: end) { [weak self] _, _ in
            if saveToHealth {
                endingBuilder.finishWorkout { _, error in
                    Task { @MainActor in
                        if let error {
                            self?.lastErrorMessage = error.localizedDescription
                        }
                    }
                }
            } else {
                endingBuilder.discardWorkout()
                Task { @MainActor in
                    self?.activity = .empty
                }
            }
        }
    }

    private func refreshActivity(from builder: HKLiveWorkoutBuilder, forcePush: Bool = false) {
        var next = RideWatchActivityMetrics.empty
        let bpmUnit = HKUnit.count().unitDivided(by: .minute())
        let rpmUnit = HKUnit.count().unitDivided(by: .minute())
        let speedUnit = HKUnit.meter().unitDivided(by: .second())

        if let type = HKQuantityType.quantityType(forIdentifier: .heartRate),
           let stats = builder.statistics(for: type) {
            next.heartRateBPM = stats.mostRecentQuantity()?.doubleValue(for: bpmUnit)
            next.averageHeartRateBPM = stats.averageQuantity()?.doubleValue(for: bpmUnit)
            next.maxHeartRateBPM = stats.maximumQuantity()?.doubleValue(for: bpmUnit)
        }
        if let type = HKQuantityType.quantityType(forIdentifier: .activeEnergyBurned),
           let stats = builder.statistics(for: type) {
            next.activeEnergyKilocalories = stats.sumQuantity()?.doubleValue(for: .kilocalorie())
        }
        if let type = HKQuantityType.quantityType(forIdentifier: .basalEnergyBurned),
           let stats = builder.statistics(for: type) {
            next.basalEnergyKilocalories = stats.sumQuantity()?.doubleValue(for: .kilocalorie())
        }
        if let type = HKQuantityType.quantityType(forIdentifier: .distanceCycling),
           let stats = builder.statistics(for: type) {
            next.watchDistanceMeters = stats.sumQuantity()?.doubleValue(for: .meter())
        }

        if #available(watchOS 10.0, *) {
            if let type = HKQuantityType.quantityType(forIdentifier: .cyclingCadence),
               let stats = builder.statistics(for: type) {
                next.cadenceRPM = stats.mostRecentQuantity()?.doubleValue(for: rpmUnit)
                next.averageCadenceRPM = stats.averageQuantity()?.doubleValue(for: rpmUnit)
            }
            if let type = HKQuantityType.quantityType(forIdentifier: .cyclingSpeed),
               let stats = builder.statistics(for: type) {
                next.cyclingSpeedMetersPerSecond = stats.mostRecentQuantity()?.doubleValue(for: speedUnit)
            }
            if let type = HKQuantityType.quantityType(forIdentifier: .cyclingPower),
               let stats = builder.statistics(for: type) {
                next.cyclingPowerWatts = stats.mostRecentQuantity()?.doubleValue(for: .watt())
                next.averageCyclingPowerWatts = stats.averageQuantity()?.doubleValue(for: .watt())
                next.maxCyclingPowerWatts = stats.maximumQuantity()?.doubleValue(for: .watt())
            }
        }

        activity = next
        pushActivityToPhoneIfNeeded(next, force: forcePush)
    }

    private func pushActivityToPhoneIfNeeded(_ metrics: RideWatchActivityMetrics, force: Bool) {
        guard metrics.hasAnyValue else { return }
        let now = ProcessInfo.processInfo.systemUptime
        guard force || now - lastMetricsPushAt >= metricsPushInterval else { return }
        lastMetricsPushAt = now
        RideWatchReceiver.shared.sendActivity(metrics)
    }

    private func ensureAuthorization() async -> Bool {
        guard HKHealthStore.isHealthDataAvailable() else { return false }

        let types = Self.collectibleQuantityTypes
        var share: Set<HKSampleType> = [HKObjectType.workoutType()]
        var read: Set<HKObjectType> = [HKObjectType.workoutType()]
        for type in types {
            share.insert(type)
            read.insert(type)
        }

        // If workout write was previously denied, don't bother re-prompting.
        if healthStore.authorizationStatus(for: HKObjectType.workoutType()) == .sharingDenied {
            return false
        }

        if !didRequestAuthorization {
            didRequestAuthorization = true
            do {
                try await healthStore.requestAuthorization(toShare: share, read: read)
            } catch {
                lastErrorMessage = error.localizedDescription
                return false
            }
        }
        return healthStore.authorizationStatus(for: HKObjectType.workoutType()) != .sharingDenied
    }

    /// Quantity types we ask HealthKit to stream into the live builder.
    private static var collectibleQuantityTypes: [HKQuantityType] {
        var identifiers: [HKQuantityTypeIdentifier] = [
            .heartRate,
            .activeEnergyBurned,
            .basalEnergyBurned,
            .distanceCycling,
        ]
        if #available(watchOS 10.0, *) {
            identifiers.append(contentsOf: [
                .cyclingCadence,
                .cyclingSpeed,
                .cyclingPower,
            ])
        }
        return identifiers.compactMap { HKQuantityType.quantityType(forIdentifier: $0) }
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
    ) {
        Task { @MainActor in
            guard self.builder === workoutBuilder else { return }
            self.refreshActivity(from: workoutBuilder)
        }
    }
}
