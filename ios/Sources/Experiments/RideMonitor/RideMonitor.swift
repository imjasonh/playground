import Foundation
import CoreMotion
import CoreLocation
import UserNotifications
#if canImport(UIKit)
import UIKit
#endif

/// Orchestrates a ride session: high-rate motion sampling for jolt/crash
/// detection, a background location session that keeps the app alive with the
/// screen locked, and full logging saved to disk on stop.
///
/// ## Why rides used to grow multi-minute sensing holes
///
/// Core Motion does **not** run while the process is suspended. The only
/// supported way to keep sampling with the screen off is continuous background
/// location (`UIBackgroundModes: location` + Always authorization +
/// `allowsBackgroundLocationUpdates = true`). Build 14 started rides under
/// When-In-Use with background updates **off**, so locking the phone mid-ride
/// suspended the process — motion, GPS, and barometer all stopped together
/// until the app was opened again. We therefore refuse to start until Always
/// is granted, hold a `CLBackgroundActivitySession` on iOS 17+, and restart
/// device-motion if location is flowing but accelerometer callbacks stall.
///
/// Core Motion updates are delivered on `OperationQueue.main` and Core Location
/// delegate callbacks arrive on the (main) thread this object is created on, so
/// every `@Published` mutation already happens on the main thread. Marked
/// `@MainActor` so Live Activity / WatchConnectivity helpers can be called
/// directly from those same paths.
@MainActor
final class RideMonitor: NSObject, ObservableObject {
    @Published private(set) var isRunning = false
    @Published private(set) var currentG = 0.0
    @Published private(set) var peakG = 0.0
    @Published private(set) var joltCount = 0
    @Published private(set) var events: [RideEvent] = []
    @Published private(set) var elapsed: TimeInterval = 0
    @Published private(set) var distanceMeters = 0.0
    /// Current GPS speed in m/s (-1 when Core Location has no reading).
    @Published private(set) var currentSpeedMetersPerSecond = -1.0
    @Published private(set) var crashAlert = false
    @Published private(set) var statusMessage = "Ready"
    /// The ride most recently saved to disk (set on stop).
    @Published private(set) var lastSavedRide: Ride?
    /// Live heart rate from the Watch workout session (nil until samples arrive).
    @Published private(set) var heartRateBPM: Double?
    /// Active energy from the Watch workout session (kilocalories).
    @Published private(set) var activeEnergyKilocalories: Double?
    /// Cadence from a paired Bluetooth sensor (rpm), when available.
    @Published private(set) var cadenceRPM: Double?
    /// Cycling power from a paired power meter (watts), when available.
    @Published private(set) var cyclingPowerWatts: Double?

    private let motion = CMMotionManager()
    private let location = CLLocationManager()
    private let altimeter = CMAltimeter()
    private let store = RideStore()
    private let liveActivity = RideLiveActivityController.shared
    private let watchSession = RideWatchPhoneSession.shared

    private var classifier = RideEventClassifier()
    private var aggregator = MotionAggregator()

    private var startUptime: TimeInterval = 0
    private var startDate = Date()
    private var timer: Timer?
    private var lastLocation: CLLocation?
    private var crashCount = 0
    /// Set when the user taps Start until recording begins or is denied.
    private var wantsRecording = false
    /// Throttle Live Activity / Watch pushes (ActivityKit has an update budget).
    private var lastCompanionPushAt: TimeInterval = 0
    /// iOS 17+ background activity session (retained for the ride). Typed as
    /// `AnyObject?` so this file still compiles against the iOS 16 deployment target.
    private var backgroundActivitySession: AnyObject?

    /// Uptime offset of the most recent motion sample (nil until the first one).
    private var lastMotionAt: TimeInterval?
    /// GPS fix last seen while motion samples were flowing — used so a burst
    /// flushed after a suspend gap is not tagged with the post-gap teleport.
    private var locationAtLastMotion: CLLocation?
    /// Latest magnitude for UI; published from the 0.25s timer (not at 50 Hz).
    private var latestG = 0.0
    /// Whole-second floor of the last persisted barometer sample.
    private var lastAltitudeSecond: Int?
    /// Ride-relative time of the last thinned GPS sample we kept.
    private var lastTrackSampleAt: TimeInterval?

    // Accumulated logs for the current ride.
    private var track: [LocationSample] = []
    private var motionSummaries: [MotionSummary] = []
    private var altitudeSamples: [AltitudeSample] = []

    // Recording diagnostics (persisted on stop + mirrored to Console).
    private var motionRestartCount = 0
    private var locationErrorCount = 0
    private var maxCompanionPushMilliseconds = 0.0
    private var lastHeartbeatMinute = -1

    private let sampleHz = 50.0
    private let companionPushInterval: TimeInterval = 1.0
    /// If sensing is silent this long, treat the ride as ended at the last sample
    /// (app was suspended / background location not keeping us alive).
    private let sensingGapEndThreshold: TimeInterval = 90
    /// Location still arriving but motion quiet this long → restart Core Motion.
    private let motionStallRestartThreshold: TimeInterval = 2.5
    /// Companion pushes slower than this are logged as warnings.
    private let companionPushWarnMilliseconds: Double = 50
    /// Persist at most one barometer / GPS sample per this interval.
    private let sensorPersistInterval: TimeInterval = 1.0

    override init() {
        super.init()
        location.delegate = self
        // Best-for-navigation keeps fixes frequent while moving, which is what
        // holds the process awake for accelerometer delivery.
        location.desiredAccuracy = kCLLocationAccuracyBestForNavigation
        location.distanceFilter = kCLDistanceFilterNone
        location.activityType = .fitness
        location.pausesLocationUpdatesAutomatically = false
        // Activate WatchConnectivity early so the companion is ready at start.
        _ = watchSession
    }

    deinit {
        // `@StateObject` teardown (navigate away) should have already called
        // `stop()` from `onDisappear`. Invalidate the RunLoop timer here as a
        // belt-and-suspenders so a leaked timer can't keep firing.
        timer?.invalidate()
    }

    private var now: TimeInterval { ProcessInfo.processInfo.systemUptime - startUptime }

    func start() {
        guard !isRunning else { return }
        guard motion.isDeviceMotionAvailable else {
            statusMessage = "Motion sensors unavailable on this device."
            RideMonitorLog.error("start refused — device motion unavailable")
            return
        }

        wantsRecording = true
        RideMonitorLog.notice(
            "start requested auth=\(Self.describeAuth(location.authorizationStatus))"
        )
        UNUserNotificationCenter.current().requestAuthorization(options: [.alert, .sound]) { _, _ in }

        switch location.authorizationStatus {
        case .notDetermined:
            statusMessage = "Waiting for Always location permission…"
            location.requestAlwaysAuthorization()
        case .authorizedAlways:
            beginRecording()
        case .authorizedWhenInUse:
            // Never start here. When-In-Use + screen lock suspends the process;
            // Core Motion and GPS both stop, which is exactly the multi-minute
            // hole we saw in production rides.
            statusMessage = """
            Ride Monitor needs “Always” location so recording continues with the screen off. \
            Choose Allow Always when prompted.
            """
            RideMonitorLog.notice("start deferred — need Always (currently WhenInUse)")
            location.requestAlwaysAuthorization()
        case .denied, .restricted:
            wantsRecording = false
            statusMessage = "Location permission is required to record rides."
            RideMonitorLog.error("start refused — location denied/restricted")
        @unknown default:
            wantsRecording = false
            statusMessage = "Location status unknown."
            RideMonitorLog.error("start refused — unknown authorization status")
        }
    }

    private func beginRecording() {
        guard wantsRecording, !isRunning else { return }
        // Hard requirement: without Always, background location keep-alive is a no-op.
        guard location.authorizationStatus == .authorizedAlways else {
            statusMessage = """
            Ride Monitor needs “Always” location so recording continues with the screen off.
            """
            RideMonitorLog.error("beginRecording refused — not Always authorized")
            return
        }

        classifier = RideEventClassifier()
        aggregator = MotionAggregator()
        events = []
        track = []
        motionSummaries = []
        altitudeSamples = []
        joltCount = 0
        crashCount = 0
        peakG = 0
        currentG = 0
        distanceMeters = 0
        currentSpeedMetersPerSecond = -1
        elapsed = 0
        crashAlert = false
        heartRateBPM = nil
        activeEnergyKilocalories = nil
        cadenceRPM = nil
        cyclingPowerWatts = nil
        watchSession.resetActivity()
        lastLocation = nil
        lastMotionAt = nil
        locationAtLastMotion = nil
        latestG = 0
        lastAltitudeSecond = nil
        lastTrackSampleAt = nil
        lastCompanionPushAt = 0
        motionRestartCount = 0
        locationErrorCount = 0
        maxCompanionPushMilliseconds = 0
        lastHeartbeatMinute = -1
        startUptime = ProcessInfo.processInfo.systemUptime
        startDate = Date()
        isRunning = true

        enableBackgroundKeepAlive()
        location.startUpdatingLocation()
        startMotionUpdates()
        startAltimeterUpdates()

        timer = Timer.scheduledTimer(withTimeInterval: 0.25, repeats: true) { [weak self] _ in
            guard let self, self.isRunning else { return }
            self.elapsed = self.now
            // Publish UI g at ~4 Hz — mutating @Published at 50 Hz on the main
            // queue was starving Core Motion delivery on longer rides.
            self.currentG = self.latestG
            self.pullWatchActivity()
            self.pollSensingHealth()
            self.pushCompanionsIfNeeded(force: false)
            self.logHeartbeatIfNeeded()
        }

        let snapshot = makeLiveSnapshot()
        liveActivity.start(startedAt: startDate, snapshot: snapshot)
        watchSession.send(snapshot)
        lastCompanionPushAt = now
        statusMessage = "Recording ride (screen-off OK)…"
        RideMonitorLog.notice(
            "recording started altimeter=\(CMAltimeter.isRelativeAltitudeAvailable()) backgroundSession=\(backgroundActivitySession != nil)"
        )
    }

    /// Continuous background location is what prevents iOS from suspending us.
    private func enableBackgroundKeepAlive() {
        location.allowsBackgroundLocationUpdates = true
        location.showsBackgroundLocationIndicator = true
        location.pausesLocationUpdatesAutomatically = false
        startBackgroundActivitySessionIfAvailable()
    }

    private func disableBackgroundKeepAlive() {
        location.allowsBackgroundLocationUpdates = false
        location.showsBackgroundLocationIndicator = false
        endBackgroundActivitySession()
    }

    private func startBackgroundActivitySessionIfAvailable() {
        endBackgroundActivitySession()
        if #available(iOS 17.0, *) {
            // Holds the blue “in use” indicator / background run state for live updates.
            backgroundActivitySession = CLBackgroundActivitySession()
        }
    }

    private func endBackgroundActivitySession() {
        if #available(iOS 17.0, *) {
            (backgroundActivitySession as? CLBackgroundActivitySession)?.invalidate()
        }
        backgroundActivitySession = nil
    }

    private func startMotionUpdates() {
        motion.stopDeviceMotionUpdates()
        motion.deviceMotionUpdateInterval = 1.0 / sampleHz
        motion.startDeviceMotionUpdates(to: .main) { [weak self] data, error in
            guard let self else { return }
            if let error {
                RideMonitorLog.error("deviceMotion error: \(error.localizedDescription)")
            }
            guard let data else { return }
            self.ingest(data)
        }
    }

    private func startAltimeterUpdates() {
        altimeter.stopRelativeAltitudeUpdates()
        guard CMAltimeter.isRelativeAltitudeAvailable() else { return }
        altimeter.startRelativeAltitudeUpdates(to: .main) { [weak self] data, error in
            guard let self else { return }
            if let error {
                RideMonitorLog.error("altimeter error: \(error.localizedDescription)")
            }
            guard let data else { return }
            if let last = self.lastMotionAt, self.now - last > self.sensingGapEndThreshold {
                return
            }
            // Match motion summaries: one barometer sample per whole second.
            // Full-rate (~50 Hz) persistence was the dominant RAM growth on long rides.
            let second = Int(self.now.rounded(.down))
            if self.lastAltitudeSecond == second { return }
            self.lastAltitudeSecond = second
            self.altitudeSamples.append(AltitudeSample(
                t: TimeInterval(second),
                relativeAltitude: data.relativeAltitude.doubleValue,
                pressureKPa: data.pressure.doubleValue
            ))
        }
    }

    /// Timer-driven stall / gap recovery — location callbacks alone can miss this
    /// when GPS also goes quiet while the process stays awake.
    private func pollSensingHealth() {
        guard isRunning else { return }
        if let last = lastMotionAt, now - last > sensingGapEndThreshold {
            finalizeAfterSensingGap()
            return
        }
        restartMotionIfStalled(requireExistingMotion: true)
    }

    /// If accelerometer callbacks stopped, kick Core Motion.
    /// - Parameter requireExistingMotion: when true (timer path), skip the
    ///   "no samples yet" restart so we don't spam before the first callback.
    private func restartMotionIfStalled(requireExistingMotion: Bool = false) {
        guard isRunning else { return }
        guard let last = lastMotionAt else {
            guard !requireExistingMotion else { return }
            motionRestartCount += 1
            RideMonitorLog.notice("motion restart #\(motionRestartCount) — no samples yet, GPS flowing")
            startMotionUpdates()
            return
        }
        let stall = now - last
        guard stall >= motionStallRestartThreshold, stall < sensingGapEndThreshold else { return }
        motionRestartCount += 1
        RideMonitorLog.notice(
            String(
                format: "motion restart #%d after %.1fs stall (gps=%d motion=%d baro=%d)",
                motionRestartCount,
                stall,
                track.count,
                motionSummaries.count,
                altitudeSamples.count
            )
        )
        startMotionUpdates()
        startAltimeterUpdates()
    }

    func stop() {
        stopRecording(endedAtOffset: sensingEndOffset(), reason: .userStopped)
    }

    /// End the ride at the last motion sample after a long sensing gap (suspend).
    private func finalizeAfterSensingGap() {
        guard isRunning, let end = lastMotionAt else { return }
        let gap = now - end
        RideMonitorLog.fault(
            String(
                format: "sensing gap auto-end lastMotion=%.1fs gap=%.1fs gps=%d motion=%d baro=%d restarts=%d locErrors=%d maxPushMs=%.1f",
                end,
                gap,
                track.count,
                motionSummaries.count,
                altitudeSamples.count,
                motionRestartCount,
                locationErrorCount,
                maxCompanionPushMilliseconds
            )
        )
        let flushed = classifier.flushOpenBurst(endingAt: end)
        append(events: flushed, location: locationAtLastMotion)
        stopRecording(
            endedAtOffset: end,
            reason: .sensingGap,
            detail: "Stopped after sensing paused — background keep-alive was lost."
        )
    }

    private func sensingEndOffset() -> TimeInterval {
        guard let last = lastMotionAt else { return elapsed }
        if elapsed - last > sensingGapEndThreshold {
            return last
        }
        return elapsed
    }

    private func stopRecording(
        endedAtOffset: TimeInterval,
        reason: RideEndReason,
        detail: String? = nil
    ) {
        guard isRunning else { return }
        wantsRecording = false
        isRunning = false
        motion.stopDeviceMotionUpdates()
        altimeter.stopRelativeAltitudeUpdates()
        location.stopUpdatingLocation()
        disableBackgroundKeepAlive()
        timer?.invalidate()
        timer = nil

        if let summary = aggregator.finish() {
            motionSummaries.append(summary)
        }

        trimLogs(after: endedAtOffset)
        // Deferred GPS fixes can arrive out of order once we stamp with
        // `loc.timestamp` instead of wall-clock `now`.
        track.sort { $0.t < $1.t }
        elapsed = endedAtOffset
        pullWatchActivity()

        let finalSnapshot = makeLiveSnapshot(isRiding: false)
        liveActivity.end(snapshot: finalSnapshot)
        watchSession.send(finalSnapshot)

        let watchActivity = watchSession.latestActivity
        let endedAt = startDate.addingTimeInterval(endedAtOffset)
        let diagnostics = RideRecordingDiagnostics(
            endReason: reason,
            endDetail: detail,
            lastMotionOffset: lastMotionAt.map { min($0, endedAtOffset) },
            lastLocationOffset: track.last.map { min($0.t, endedAtOffset) },
            motionRestartCount: motionRestartCount,
            locationErrorCount: locationErrorCount,
            maxCompanionPushMilliseconds: maxCompanionPushMilliseconds > 0
                ? maxCompanionPushMilliseconds
                : nil,
            authorizationStatusAtEnd: Self.describeAuth(location.authorizationStatus)
        )
        // Events are appended chronologically during the ride.
        let ride = RideSampleSanitizer.sanitize(
            Ride(
                id: UUID(),
                startedAt: startDate,
                endedAt: endedAt,
                durationSeconds: endedAtOffset,
                distanceMeters: distanceMeters,
                peakG: peakG,
                joltCount: joltCount,
                crashCount: crashCount,
                averageHeartRateBPM: watchActivity.averageHeartRateBPM,
                maxHeartRateBPM: watchActivity.maxHeartRateBPM,
                activeEnergyKilocalories: watchActivity.activeEnergyKilocalories,
                basalEnergyKilocalories: watchActivity.basalEnergyKilocalories,
                watchDistanceMeters: watchActivity.watchDistanceMeters,
                averageCadenceRPM: watchActivity.averageCadenceRPM,
                averageCyclingPowerWatts: watchActivity.averageCyclingPowerWatts,
                maxCyclingPowerWatts: watchActivity.maxCyclingPowerWatts,
                recordingDiagnostics: diagnostics,
                events: events,
                track: track,
                motion: motionSummaries,
                barometer: altitudeSamples
            )
        )

        RideMonitorLog.notice(
            String(
                format: "recording stopped reason=%@ duration=%.1fs distance=%.0fm gps=%d motion=%d baro=%d events=%d restarts=%d locErrors=%d maxPushMs=%.1f auth=%@",
                reason.rawValue,
                endedAtOffset,
                distanceMeters,
                track.count,
                motionSummaries.count,
                altitudeSamples.count,
                ride.events.count,
                motionRestartCount,
                locationErrorCount,
                maxCompanionPushMilliseconds,
                diagnostics.authorizationStatusAtEnd ?? "?"
            )
        )

        do {
            try store.save(ride)
            lastSavedRide = ride
            let base = "Ride saved — \(ride.events.count) event(s), \(ride.track.count) GPS fixes."
            statusMessage = detail.map { "\(base) \($0)" } ?? base
            // On-device label is async (Foundation Models when available).
            Task { await attachSummary(to: ride, statusSuffix: detail) }
        } catch {
            // Keep the sanitized ride in memory so Past rides / export can still
            // reach it if the user stays in the experiment after a disk failure.
            lastSavedRide = ride
            statusMessage = "Ride finished but couldn't be saved: \(error.localizedDescription)"
            RideMonitorLog.error("ride save failed: \(error.localizedDescription)")
        }
    }

    /// Generate a few-word summary and rewrite the saved ride JSON.
    /// Leaves `summary` unset when the on-device model is unavailable or fails.
    private func attachSummary(to ride: Ride, statusSuffix: String?) async {
        guard let text = await RideSummaryGenerator.summarize(for: ride) else { return }
        var updated = ride
        updated.summary = text
        do {
            try store.save(updated)
            if lastSavedRide?.id == updated.id {
                lastSavedRide = updated
            }
            if !isRunning {
                let base = "Ride saved — \(text)"
                statusMessage = statusSuffix.map { "\(base) \($0)" } ?? base
            }
        } catch {
            RideMonitorLog.error("summary save failed: \(error.localizedDescription)")
        }
    }

    /// Drop samples that arrived after the ride's sensing end (post-gap GPS, etc.).
    private func trimLogs(after end: TimeInterval) {
        track.removeAll { $0.t > end + 0.01 }
        motionSummaries.removeAll { $0.t > end + 0.01 }
        altitudeSamples.removeAll { $0.t > end + 0.01 }
        events.removeAll { $0.at > end + 0.01 }
        joltCount = events.filter { $0.severity != .crash }.count
        crashCount = events.filter { $0.severity == .crash }.count
        peakG = events.map(\.peakG).max() ?? peakG
        if let motionPeak = motionSummaries.map(\.peakG).max() {
            peakG = max(peakG, motionPeak)
        }
    }

    private func makeLiveSnapshot(isRiding: Bool? = nil) -> RideLiveSnapshot {
        RideLiveSnapshot(
            isRiding: isRiding ?? isRunning,
            startedAt: startDate,
            elapsedSeconds: elapsed,
            distanceMeters: distanceMeters,
            currentSpeedMetersPerSecond: currentSpeedMetersPerSecond,
            profile: RideProfileBuilder.build(altitudes: altitudeSamples, track: track)
        )
    }

    private func pushCompanionsIfNeeded(force: Bool) {
        guard isRunning else { return }
        let t = now
        guard force || t - lastCompanionPushAt >= companionPushInterval else { return }
        lastCompanionPushAt = t
        pullWatchActivity()

        let started = ProcessInfo.processInfo.systemUptime
        let snapshot = makeLiveSnapshot()
        liveActivity.update(snapshot: snapshot)
        watchSession.send(snapshot)
        let pushMs = (ProcessInfo.processInfo.systemUptime - started) * 1000
        if pushMs > maxCompanionPushMilliseconds {
            maxCompanionPushMilliseconds = pushMs
        }
        if pushMs >= companionPushWarnMilliseconds {
            RideMonitorLog.notice(
                String(
                    format: "slow companion push %.1fms at t=%.1fs baro=%d gps=%d",
                    pushMs,
                    t,
                    altitudeSamples.count,
                    track.count
                )
            )
        }
    }

    private func logHeartbeatIfNeeded() {
        let minute = Int(elapsed / 60)
        guard minute > 0, minute != lastHeartbeatMinute else { return }
        lastHeartbeatMinute = minute
        let motionAge = lastMotionAt.map { elapsed - $0 } ?? -1
        let locationAge = track.last.map { elapsed - $0.t } ?? -1
        RideMonitorLog.info(
            String(
                format: "heartbeat min=%d elapsed=%.0fs gps=%d motion=%d baro=%d motionAge=%.1fs locAge=%.1fs restarts=%d locErrors=%d maxPushMs=%.1f",
                minute,
                elapsed,
                track.count,
                motionSummaries.count,
                altitudeSamples.count,
                motionAge,
                locationAge,
                motionRestartCount,
                locationErrorCount,
                maxCompanionPushMilliseconds
            )
        )
    }

    private func pullWatchActivity() {
        let activity = watchSession.latestActivity
        heartRateBPM = activity.heartRateBPM
        activeEnergyKilocalories = activity.activeEnergyKilocalories
        cadenceRPM = activity.cadenceRPM
        cyclingPowerWatts = activity.cyclingPowerWatts
    }

    func dismissCrashAlert() {
        crashAlert = false
    }

    /// Called when the scene becomes active again (foreground).
    func handleSceneBecameActive() {
        RideMonitorLog.info(
            "scene active running=\(isRunning) auth=\(Self.describeAuth(location.authorizationStatus))"
        )
        if isRunning {
            liveActivity.update(snapshot: makeLiveSnapshot())
            if location.authorizationStatus != .authorizedAlways {
                endRideAfterLosingKeepAlive(
                    reason: .alwaysRequiredOnForeground,
                    message: """
                    Ride ended — “Always” location is required to keep sensing with the screen off.
                    """
                )
                return
            }
            enableBackgroundKeepAlive()
            restartMotionIfStalled()
            if let last = lastMotionAt, now - last > sensingGapEndThreshold {
                finalizeAfterSensingGap()
                return
            }
        }
        liveActivity.handleSceneBecameActive()
        guard isRunning else { return }
        pushCompanionsIfNeeded(force: true)
    }

    /// Called when the scene leaves the foreground. Re-assert keep-alive; if we
    /// somehow lost Always, end the ride instead of recording a silent hole.
    func handleSceneEnteredBackground() {
        guard isRunning else { return }
        RideMonitorLog.info(
            "scene background auth=\(Self.describeAuth(location.authorizationStatus)) elapsed=\(String(format: "%.1f", elapsed))"
        )
        guard location.authorizationStatus == .authorizedAlways else {
            endRideAfterLosingKeepAlive(
                reason: .backgroundWithoutAlways,
                message: """
                Ride ended when leaving the app — enable “Always” location for screen-off recording.
                """
            )
            return
        }
        enableBackgroundKeepAlive()
    }

    private func endRideAfterLosingKeepAlive(reason: RideEndReason, message: String) {
        RideMonitorLog.fault("keep-alive lost reason=\(reason.rawValue) — \(message)")
        if lastMotionAt != nil {
            // Prefer truncating at last motion when we already have samples, but
            // still persist the more specific permission/lifecycle reason.
            let end = lastMotionAt ?? elapsed
            let flushed = classifier.flushOpenBurst(endingAt: end)
            append(events: flushed, location: locationAtLastMotion)
            stopRecording(endedAtOffset: end, reason: reason, detail: message)
        } else {
            stopRecording(endedAtOffset: elapsed, reason: reason, detail: message)
        }
        statusMessage = message
    }

    private func ingest(_ data: CMDeviceMotion) {
        guard isRunning else { return }

        let t = now

        if let last = lastMotionAt, t - last > sensingGapEndThreshold {
            finalizeAfterSensingGap()
            return
        }

        if let last = lastMotionAt, t - last > classifier.thresholds.maxSampleGap {
            let flushed = classifier.flushOpenBurst(endingAt: last)
            append(events: flushed, location: locationAtLastMotion)
        }

        let a = data.userAcceleration // gravity already removed, in g
        let magnitude = (a.x * a.x + a.y * a.y + a.z * a.z).squareRoot()
        let r = data.rotationRate
        let rotation = (r.x * r.x + r.y * r.y + r.z * r.z).squareRoot()

        // Don't publish `currentG` here — 50 Hz @Published updates rebuild SwiftUI
        // on the same queue that delivers Core Motion. The timer mirrors `latestG`.
        latestG = magnitude
        if magnitude > peakG {
            peakG = magnitude
        }

        if let summary = aggregator.add(t: t, g: magnitude, rotation: rotation) {
            motionSummaries.append(summary)
        }

        let newEvents = classifier.process(magnitude: magnitude, at: t)
        append(events: newEvents, location: locationAtLastMotion ?? lastLocation)

        lastMotionAt = t
        if let loc = lastLocation, loc.horizontalAccuracy >= 0, loc.horizontalAccuracy <= 50 {
            locationAtLastMotion = loc
        }
    }

    private func append(events newEvents: [RideEvent], location: CLLocation?) {
        for var event in newEvents {
            event.latitude = location?.coordinate.latitude
            event.longitude = location?.coordinate.longitude
            events.append(event)
            if event.severity == .crash {
                crashCount += 1
                handleCrash(event)
            } else {
                joltCount += 1
            }
        }
    }

    private func handleCrash(_ event: RideEvent) {
        crashAlert = true
        statusMessage = "Possible crash detected!"
        RideMonitorLog.notice(
            String(format: "crash event peakG=%.2f at=%.1fs", event.peakG, event.at)
        )
        #if canImport(UIKit)
        UINotificationFeedbackGenerator().notificationOccurred(.error)
        #endif
        let content = UNMutableNotificationContent()
        content.title = "Possible crash detected"
        content.body = String(format: "A %.1fg impact was followed by stillness.", event.peakG)
        content.sound = .default
        let request = UNNotificationRequest(identifier: event.id.uuidString, content: content, trigger: nil)
        UNUserNotificationCenter.current().add(request)
    }

    private static func describeAuth(_ status: CLAuthorizationStatus) -> String {
        switch status {
        case .notDetermined: return "notDetermined"
        case .restricted: return "restricted"
        case .denied: return "denied"
        case .authorizedAlways: return "always"
        case .authorizedWhenInUse: return "whenInUse"
        @unknown default: return "unknown"
        }
    }
}

extension RideMonitor: CLLocationManagerDelegate {
    func locationManagerDidChangeAuthorization(_ manager: CLLocationManager) {
        let auth = Self.describeAuth(manager.authorizationStatus)
        RideMonitorLog.notice(
            "authorization changed → \(auth) wantsRecording=\(wantsRecording) running=\(isRunning)"
        )
        guard wantsRecording else { return }

        switch manager.authorizationStatus {
        case .authorizedAlways:
            if isRunning {
                enableBackgroundKeepAlive()
            } else {
                beginRecording()
            }
        case .authorizedWhenInUse:
            if isRunning {
                // Downgraded mid-ride — cannot keep sensing with the screen off.
                endRideAfterLosingKeepAlive(
                    reason: .locationLimitedToWhenInUse,
                    message: """
                    Ride ended — location was limited to While Using. Enable “Always” in Settings for screen-off rides.
                    """
                )
            } else {
                statusMessage = """
                Ride Monitor needs “Always” location so recording continues with the screen off. \
                Choose Allow Always when prompted (or enable it in Settings).
                """
            }
        case .denied, .restricted:
            wantsRecording = false
            if isRunning {
                endRideAfterLosingKeepAlive(
                    reason: .locationDenied,
                    message: "Ride ended — location permission is required to record rides."
                )
            } else {
                statusMessage = "Location permission is required to record rides."
            }
        default:
            break
        }
    }

    func locationManager(_ manager: CLLocationManager, didUpdateLocations locations: [CLLocation]) {
        guard isRunning else { return }

        if let last = lastMotionAt, now - last > sensingGapEndThreshold {
            finalizeAfterSensingGap()
            return
        }

        // Location without motion usually means CMMotionManager wedged after a
        // brief suspend — restart it while we still have a background hold.
        restartMotionIfStalled(requireExistingMotion: false)

        for loc in locations {
            if let previous = lastLocation {
                let step = loc.distance(from: previous)
                if step.isFinite, step < 500 { // ignore obvious GPS jumps
                    distanceMeters += step
                }
            }
            lastLocation = loc
            currentSpeedMetersPerSecond = loc.speed

            // Prefer Core Location's timestamp so batched / deferred fixes don't
            // all collapse onto the same `now`. Thin to ~1 Hz for persistence.
            let sampleT = max(0, loc.timestamp.timeIntervalSince(startDate))
            let shouldPersist: Bool = {
                guard let last = lastTrackSampleAt else { return true }
                return sampleT - last >= sensorPersistInterval
            }()
            if shouldPersist {
                lastTrackSampleAt = sampleT
                track.append(LocationSample(
                    t: sampleT,
                    latitude: loc.coordinate.latitude,
                    longitude: loc.coordinate.longitude,
                    altitude: loc.altitude,
                    horizontalAccuracy: loc.horizontalAccuracy,
                    verticalAccuracy: loc.verticalAccuracy,
                    speed: loc.speed,
                    course: loc.course
                ))
            }
            if lastMotionAt != nil, loc.horizontalAccuracy >= 0, loc.horizontalAccuracy <= 50 {
                locationAtLastMotion = loc
            }
        }
        pushCompanionsIfNeeded(force: false)
    }

    func locationManager(_ manager: CLLocationManager, didFailWithError error: Error) {
        locationErrorCount += 1
        RideMonitorLog.error(
            "location error #\(locationErrorCount): \(error.localizedDescription) elapsed=\(String(format: "%.1f", elapsed))"
        )
    }
}
