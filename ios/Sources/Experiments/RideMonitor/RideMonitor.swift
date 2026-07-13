import Foundation
import CoreMotion
import CoreLocation
import UserNotifications
#if canImport(UIKit)
import UIKit
#endif

/// Orchestrates a ride session: high-rate motion sampling for jolt/crash
/// detection, a background location session (requires “Always” location
/// permission) that keeps the app alive with the screen locked, and full logging
/// (location track, per-second motion summaries, barometric altitude, and events)
/// which is saved to disk on stop.
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

    /// Uptime offset of the most recent motion sample (nil until the first one).
    private var lastMotionAt: TimeInterval?
    /// GPS fix last seen while motion samples were flowing — used so a burst
    /// flushed after a suspend gap is not tagged with the post-gap teleport.
    private var locationAtLastMotion: CLLocation?

    // Accumulated logs for the current ride.
    private var track: [LocationSample] = []
    private var motionSummaries: [MotionSummary] = []
    private var altitudeSamples: [AltitudeSample] = []

    private let sampleHz = 50.0
    private let companionPushInterval: TimeInterval = 1.0
    /// If sensing is silent this long, treat the ride as ended at the last sample
    /// (app was suspended / background location not keeping us alive).
    private let sensingGapEndThreshold: TimeInterval = 90

    override init() {
        super.init()
        location.delegate = self
        location.desiredAccuracy = kCLLocationAccuracyBest
        location.activityType = .fitness
        // Activate WatchConnectivity early so the companion is ready at start.
        _ = watchSession
    }

    private var now: TimeInterval { ProcessInfo.processInfo.systemUptime - startUptime }

    func start() {
        guard !isRunning else { return }
        guard motion.isDeviceMotionAvailable else {
            statusMessage = "Motion sensors unavailable on this device."
            return
        }

        wantsRecording = true
        UNUserNotificationCenter.current().requestAuthorization(options: [.alert, .sound]) { _, _ in }

        switch location.authorizationStatus {
        case .notDetermined:
            statusMessage = "Waiting for location permission…"
            // Always is required to keep Core Motion alive with the screen off.
            location.requestAlwaysAuthorization()
        case .authorizedAlways:
            beginRecording(backgroundCapable: true)
        case .authorizedWhenInUse:
            // Upgrade prompt; do not start until Always is granted — otherwise
            // the OS suspends us on lock and the ride grows a multi-minute hole.
            statusMessage = """
            Ride Monitor needs “Always” location so recording continues with the screen off. \
            Choose Allow Always when prompted.
            """
            location.requestAlwaysAuthorization()
        case .denied, .restricted:
            wantsRecording = false
            statusMessage = "Location permission is required to record rides."
        @unknown default:
            wantsRecording = false
            statusMessage = "Location status unknown."
        }
    }

    private func beginRecording(backgroundCapable: Bool) {
        guard wantsRecording, !isRunning else { return }

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
        lastLocation = nil
        lastMotionAt = nil
        locationAtLastMotion = nil
        lastCompanionPushAt = 0
        startUptime = ProcessInfo.processInfo.systemUptime
        startDate = Date()
        isRunning = true

        configureBackgroundLocation(enabled: backgroundCapable)
        location.pausesLocationUpdatesAutomatically = false
        location.startUpdatingLocation()

        motion.deviceMotionUpdateInterval = 1.0 / sampleHz
        motion.startDeviceMotionUpdates(to: .main) { [weak self] data, _ in
            guard let self, let data else { return }
            self.ingest(data)
        }

        if CMAltimeter.isRelativeAltitudeAvailable() {
            altimeter.startRelativeAltitudeUpdates(to: .main) { [weak self] data, _ in
                guard let self, let data else { return }
                // Drop barometer samples that arrive after a long sensing gap;
                // finalizeAfterSensingGap / stop handles ending the ride.
                if let last = self.lastMotionAt, self.now - last > self.sensingGapEndThreshold {
                    return
                }
                self.altitudeSamples.append(AltitudeSample(
                    t: self.now,
                    relativeAltitude: data.relativeAltitude.doubleValue,
                    pressureKPa: data.pressure.doubleValue
                ))
            }
        }

        timer = Timer.scheduledTimer(withTimeInterval: 0.25, repeats: true) { [weak self] _ in
            guard let self, self.isRunning else { return }
            self.elapsed = self.now
            self.pushCompanionsIfNeeded(force: false)
        }

        let snapshot = makeLiveSnapshot()
        liveActivity.start(startedAt: startDate, snapshot: snapshot)
        watchSession.send(snapshot)
        lastCompanionPushAt = now
    }

    private func configureBackgroundLocation(enabled: Bool) {
        if enabled {
            // Keeps the process alive so Core Motion can keep sampling with the screen off.
            location.allowsBackgroundLocationUpdates = true
            location.showsBackgroundLocationIndicator = true
            statusMessage = "Recording ride…"
        } else {
            location.allowsBackgroundLocationUpdates = false
            location.showsBackgroundLocationIndicator = false
            statusMessage = """
            Recording ride… Choose “Always” for location so logging continues with the screen off.
            """
        }
    }

    func stop() {
        stopRecording(endedAtOffset: sensingEndOffset(), statusSuffix: nil)
    }

    /// End the ride at the last motion sample after a long sensing gap (suspend).
    private func finalizeAfterSensingGap() {
        guard isRunning, let end = lastMotionAt else { return }
        let flushed = classifier.flushOpenBurst(endingAt: end)
        append(events: flushed, location: locationAtLastMotion)
        stopRecording(
            endedAtOffset: end,
            statusSuffix: "Stopped after sensing paused (enable Always location for screen-off rides)."
        )
    }

    private func sensingEndOffset() -> TimeInterval {
        guard let last = lastMotionAt else { return elapsed }
        // Manual stop after a long hole: don't pad duration with suspended time.
        if elapsed - last > sensingGapEndThreshold {
            return last
        }
        return elapsed
    }

    private func stopRecording(endedAtOffset: TimeInterval, statusSuffix: String?) {
        guard isRunning else { return }
        wantsRecording = false
        isRunning = false
        motion.stopDeviceMotionUpdates()
        altimeter.stopRelativeAltitudeUpdates()
        location.stopUpdatingLocation()
        location.allowsBackgroundLocationUpdates = false
        location.showsBackgroundLocationIndicator = false
        timer?.invalidate()
        timer = nil

        if let summary = aggregator.finish() {
            motionSummaries.append(summary)
        }

        trimLogs(after: endedAtOffset)
        elapsed = endedAtOffset

        let finalSnapshot = makeLiveSnapshot(isRiding: false)
        liveActivity.end(snapshot: finalSnapshot)
        watchSession.send(finalSnapshot)

        let endedAt = startDate.addingTimeInterval(endedAtOffset)
        let ride = Ride(
            id: UUID(),
            startedAt: startDate,
            endedAt: endedAt,
            durationSeconds: endedAtOffset,
            distanceMeters: distanceMeters,
            peakG: peakG,
            joltCount: joltCount,
            crashCount: crashCount,
            events: events.reversed(), // store chronologically
            track: track,
            motion: motionSummaries,
            barometer: altitudeSamples
        )

        do {
            try store.save(ride)
            lastSavedRide = ride
            let base = "Ride saved — \(ride.events.count) event(s), \(ride.track.count) GPS fixes."
            statusMessage = statusSuffix.map { "\(base) \($0)" } ?? base
        } catch {
            statusMessage = "Ride finished but couldn't be saved: \(error.localizedDescription)"
        }
    }

    /// Drop samples that arrived after the ride's sensing end (post-gap GPS, etc.).
    private func trimLogs(after end: TimeInterval) {
        track.removeAll { $0.t > end + 0.01 }
        motionSummaries.removeAll { $0.t > end + 0.01 }
        altitudeSamples.removeAll { $0.t > end + 0.01 }
        events.removeAll { $0.at > end + 0.01 }
        // Recompute jolt/crash counts from the trimmed event list (UI order is newest-first).
        joltCount = events.filter { $0.severity != .crash }.count
        crashCount = events.filter { $0.severity == .crash }.count
        peakG = events.map(\.peakG).max() ?? peakG
        // Also consider motion peaks in case events were sparse.
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
        let snapshot = makeLiveSnapshot()
        liveActivity.update(snapshot: snapshot)
        watchSession.send(snapshot)
    }

    func dismissCrashAlert() {
        crashAlert = false
    }

    /// Retry a Live Activity that couldn't start while backgrounded (e.g. the
    /// user granted Always location from Settings) and refresh the Watch.
    func handleSceneBecameActive() {
        if isRunning {
            // Keep any deferred start payload current before retrying request.
            liveActivity.update(snapshot: makeLiveSnapshot())
            // Opening the app after a long suspend should finalize, not append junk.
            if let last = lastMotionAt, now - last > sensingGapEndThreshold {
                finalizeAfterSensingGap()
                return
            }
        }
        liveActivity.handleSceneBecameActive()
        guard isRunning else { return }
        pushCompanionsIfNeeded(force: true)
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

        currentG = magnitude
        peakG = max(peakG, magnitude)

        if let summary = aggregator.add(t: t, g: magnitude, rotation: rotation) {
            motionSummaries.append(summary)
        }

        let newEvents = classifier.process(magnitude: magnitude, at: t)
        // Prefer the fix from active sensing; fall back to the latest GPS.
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
            events.insert(event, at: 0)
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
}

extension RideMonitor: CLLocationManagerDelegate {
    func locationManagerDidChangeAuthorization(_ manager: CLLocationManager) {
        guard wantsRecording else { return }

        switch manager.authorizationStatus {
        case .authorizedAlways:
            if isRunning {
                configureBackgroundLocation(enabled: true)
            } else {
                beginRecording(backgroundCapable: true)
            }
        case .authorizedWhenInUse:
            // Still waiting on the Always upgrade — do not start a half-broken ride.
            if !isRunning {
                statusMessage = """
                Ride Monitor needs “Always” location so recording continues with the screen off. \
                Choose Allow Always when prompted (or enable it in Settings).
                """
            }
        case .denied, .restricted:
            wantsRecording = false
            statusMessage = "Location permission is required to record rides."
        default:
            break
        }
    }

    func locationManager(_ manager: CLLocationManager, didUpdateLocations locations: [CLLocation]) {
        guard isRunning else { return }

        // Post-suspend GPS can arrive before motion; end the ride instead of
        // appending a teleport and junk fixes.
        if let last = lastMotionAt, now - last > sensingGapEndThreshold {
            finalizeAfterSensingGap()
            return
        }

        for loc in locations {
            if let previous = lastLocation {
                let step = loc.distance(from: previous)
                if step.isFinite, step < 500 { // ignore obvious GPS jumps
                    distanceMeters += step
                }
            }
            lastLocation = loc
            currentSpeedMetersPerSecond = loc.speed
            track.append(LocationSample(
                t: now,
                latitude: loc.coordinate.latitude,
                longitude: loc.coordinate.longitude,
                altitude: loc.altitude,
                horizontalAccuracy: loc.horizontalAccuracy,
                verticalAccuracy: loc.verticalAccuracy,
                speed: loc.speed,
                course: loc.course
            ))
            // Keep event geotags current while we are actively sensing.
            if lastMotionAt != nil, loc.horizontalAccuracy >= 0, loc.horizontalAccuracy <= 50 {
                locationAtLastMotion = loc
            }
        }
        pushCompanionsIfNeeded(force: false)
    }

    func locationManager(_ manager: CLLocationManager, didFailWithError error: Error) {}
}
