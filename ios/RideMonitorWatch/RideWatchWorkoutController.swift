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
/// Invariant: while the phone ride is active (`wantsSession`), keep trying to
/// hold a usable `HKWorkoutSession`. WC sync is authoritative for ride
/// start/stop; phone `startWatchApp` redelivers configuration for Crown
/// dismissal / relaunch. Lost sessions are retried on the next ensure
/// (WC update, relaunch, or scene activation) with a short cooldown.
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
    /// Coalesces concurrent ensure Tasks from rapid WC updates.
    private var isStarting = false
    /// Phone ride still wants a frontmost session (independent of HK state).
    private var wantsSession = false
    /// `false` once WC has reported idle — blocks late `startWatchApp` handles.
    private var phoneSaysRiding: Bool?
    private var rideStartedAt = Date()
    /// Start attempts for the current ride; reset only when the ride ends.
    private var startAttemptsThisRide = 0
    private var lastStartAttemptAt: Date?
    /// If the Watch launches long after the phone ride started, HealthKit can
    /// reject an old `startActivity(with:)` date — clamp past that skew.
    private let maxStartSkew: TimeInterval = 30

    private override init() {
        super.init()
    }

    /// Start (or keep) a cycling workout session while a ride is active.
    func sync(isRiding: Bool, startedAt: Date) {
        phoneSaysRiding = isRiding
        if isRiding {
            wantsSession = true
            rideStartedAt = startedAt
            ensureSession()
        } else {
            wantsSession = false
            startAttemptsThisRide = 0
            lastStartAttemptAt = nil
            endIfNeeded(saveToHealth: true)
        }
    }

    /// Invoked when the phone calls `HKHealthStore.startWatchApp`.
    func handle(_ configuration: HKWorkoutConfiguration) {
        // WC sync is authoritative for end-of-ride; ignore a late relaunch.
        if phoneSaysRiding == false { return }
        wantsSession = true
        ensureSession(configuration: configuration)
    }

    /// Re-attach to a workout that survived a Watch app crash / termination.
    func recoverActiveSessionIfNeeded() {
        healthStore.recoverActiveWorkoutSession { [weak self] recovered, error in
            Task { @MainActor in
                guard let self else { return }
                guard error == nil, let recovered else { return }
                // Don't fight an in-flight start or a session we already own.
                guard !self.isStarting, !self.hasUsableSession else { return }
                switch recovered.state {
                case .running, .paused, .prepared:
                    if self.phoneSaysRiding == false { return }
                    self.wantsSession = true
                    self.adoptRecoveredSession(recovered)
                default:
                    break
                }
            }
        }
    }

    /// Scene became active — ensure we still hold a session if the ride wants one.
    func reassertIfNeeded() {
        ensureSession()
    }

    private var hasUsableSession: Bool {
        guard let session else { return false }
        switch session.state {
        case .running, .paused, .prepared:
            return true
        default:
            return false
        }
    }

    private func ensureSession(configuration: HKWorkoutConfiguration? = nil) {
        guard wantsSession else { return }
        if hasUsableSession {
            isSessionActive = true
            return
        }
        guard !isStarting else { return }

        let now = Date()
        guard RideWatchFrontmostPolicy.shouldAttemptStart(
            wantsSession: wantsSession,
            attemptCount: startAttemptsThisRide,
            lastAttemptAt: lastStartAttemptAt,
            now: now
        ) else {
            if wantsSession,
               startAttemptsThisRide >= RideWatchFrontmostPolicy.maxStartAttemptsPerRide {
                lastErrorMessage = lastErrorMessage
                    ?? "Could not keep Ride Monitor on-wrist. Open it from the Watch app list."
            }
            return
        }

        lastStartAttemptAt = now
        startAttemptsThisRide += 1
        isStarting = true
        let startedAt = rideStartedAt
        Task {
            defer { isStarting = false }
            let authorized = await ensureAuthorization()
            guard wantsSession else { return }
            guard authorized else {
                lastErrorMessage = "Health access is required to keep Ride Monitor on-wrist and collect activity data."
                return
            }
            if hasUsableSession {
                isSessionActive = true
                return
            }
            do {
                try beginSession(
                    startedAt: startedAt,
                    configuration: configuration ?? Self.cyclingConfiguration()
                )
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

        // Use "now" when the phone's start date is far in the past (Watch
        // launched late). Keep a recent phone start so elapsed stays aligned.
        let now = Date()
        let sessionStart = startedAt < now.addingTimeInterval(-maxStartSkew) ? now : startedAt

        session.startActivity(with: sessionStart)
        builder.beginCollection(withStart: sessionStart) { [weak self] success, error in
            Task { @MainActor in
                guard let self, self.session === session else { return }
                if let error {
                    self.lastErrorMessage = error.localizedDescription
                }
                self.isSessionActive = success
                if !success {
                    // Leave session cleared so the next ensure can retry.
                    self.handleUnexpectedSessionLoss(retryImmediately: false)
                }
            }
        }
        isSessionActive = true
        lastErrorMessage = nil
    }

    private func adoptRecoveredSession(_ recovered: HKWorkoutSession) {
        if let session, session !== recovered {
            endIfNeeded(saveToHealth: false)
        }

        let builder = recovered.associatedWorkoutBuilder()
        let configuration = recovered.workoutConfiguration
        let dataSource = HKLiveWorkoutDataSource(
            healthStore: healthStore,
            workoutConfiguration: configuration
        )
        for type in Self.collectibleQuantityTypes {
            dataSource.enableCollection(for: type, predicate: nil)
        }
        builder.dataSource = dataSource
        recovered.delegate = self
        builder.delegate = self

        session = recovered
        self.builder = builder
        isSessionActive = recovered.state == .running || recovered.state == .paused || recovered.state == .prepared
        lastErrorMessage = nil
        refreshActivity(from: builder)
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

    private func handleUnexpectedSessionLoss(retryImmediately: Bool = true) {
        let orphanSession = session
        let orphanBuilder = builder
        session = nil
        builder = nil
        isSessionActive = false
        // Tear down a still-live session (e.g. beginCollection failed); skip
        // if HealthKit already ended it (delegate `.ended` / `.stopped`).
        if let orphanSession {
            switch orphanSession.state {
            case .running, .paused:
                orphanSession.stopActivity(with: Date())
                orphanSession.end()
            case .prepared:
                orphanSession.end()
            default:
                break
            }
        }
        // Discard rather than finish — this wasn't a clean end-of-ride stop.
        orphanBuilder?.discardWorkout()
        if retryImmediately {
            ensureSession()
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
                // Intentional `endIfNeeded` nils `session` before stop/end, so
                // this path is an unexpected system/user teardown.
                self.handleUnexpectedSessionLoss()
            }
        }
    }

    nonisolated func workoutSession(_ workoutSession: HKWorkoutSession, didFailWithError error: Error) {
        Task { @MainActor in
            guard self.session === workoutSession else { return }
            self.lastErrorMessage = error.localizedDescription
            self.handleUnexpectedSessionLoss()
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
