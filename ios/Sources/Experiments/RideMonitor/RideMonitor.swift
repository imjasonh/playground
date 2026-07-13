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
/// every `@Published` mutation already happens on the main thread.
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

    // Accumulated logs for the current ride.
    private var track: [LocationSample] = []
    private var motionSummaries: [MotionSummary] = []
    private var altitudeSamples: [AltitudeSample] = []

    private let sampleHz = 50.0
    private let companionPushInterval: TimeInterval = 1.0

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
            location.requestAlwaysAuthorization()
        case .authorizedAlways:
            beginRecording(backgroundCapable: true)
        case .authorizedWhenInUse:
            // Offer the upgrade to Always so motion keeps sampling with the screen off.
            location.requestAlwaysAuthorization()
            beginRecording(backgroundCapable: false)
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

        let finalSnapshot = makeLiveSnapshot(isRiding: false)
        liveActivity.end(snapshot: finalSnapshot)
        watchSession.send(finalSnapshot)

        let ride = Ride(
            id: UUID(),
            startedAt: startDate,
            endedAt: Date(),
            durationSeconds: elapsed,
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
            statusMessage = "Ride saved — \(events.count) event(s), \(track.count) GPS fixes."
        } catch {
            statusMessage = "Ride finished but couldn't be saved: \(error.localizedDescription)"
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

    private func ingest(_ data: CMDeviceMotion) {
        let a = data.userAcceleration // gravity already removed, in g
        let magnitude = (a.x * a.x + a.y * a.y + a.z * a.z).squareRoot()
        let r = data.rotationRate
        let rotation = (r.x * r.x + r.y * r.y + r.z * r.z).squareRoot()

        currentG = magnitude
        peakG = max(peakG, magnitude)

        let t = now

        if let summary = aggregator.add(t: t, g: magnitude, rotation: rotation) {
            motionSummaries.append(summary)
        }

        for var event in classifier.process(magnitude: magnitude, at: t) {
            event.latitude = lastLocation?.coordinate.latitude
            event.longitude = lastLocation?.coordinate.longitude
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
            if !isRunning {
                beginRecording(backgroundCapable: false)
            }
        case .denied, .restricted:
            wantsRecording = false
            statusMessage = "Location permission is required to record rides."
        default:
            break
        }
    }

    func locationManager(_ manager: CLLocationManager, didUpdateLocations locations: [CLLocation]) {
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
        }
        pushCompanionsIfNeeded(force: false)
    }

    func locationManager(_ manager: CLLocationManager, didFailWithError error: Error) {}
}
