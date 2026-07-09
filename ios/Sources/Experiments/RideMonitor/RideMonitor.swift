import Foundation
import CoreMotion
import CoreLocation
import UserNotifications
#if canImport(UIKit)
import UIKit
#endif

/// Orchestrates a ride session: high-rate motion sampling for jolt/crash
/// detection, a background location session that keeps the app alive with the
/// screen locked, and full logging (location track, per-second motion summaries,
/// barometric altitude, and events) which is saved to disk on stop.
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
    @Published private(set) var crashAlert = false
    @Published private(set) var statusMessage = "Ready"
    /// The ride most recently saved to disk (set on stop).
    @Published private(set) var lastSavedRide: Ride?

    private let motion = CMMotionManager()
    private let location = CLLocationManager()
    private let altimeter = CMAltimeter()
    private let store = RideStore()

    private var classifier = RideEventClassifier()
    private var aggregator = MotionAggregator()

    private var startUptime: TimeInterval = 0
    private var startDate = Date()
    private var timer: Timer?
    private var lastLocation: CLLocation?
    private var crashCount = 0

    // Accumulated logs for the current ride.
    private var track: [LocationSample] = []
    private var motionSummaries: [MotionSummary] = []
    private var altitudeSamples: [AltitudeSample] = []

    private let sampleHz = 50.0

    override init() {
        super.init()
        location.delegate = self
        location.desiredAccuracy = kCLLocationAccuracyBest
        location.activityType = .fitness
    }

    private var now: TimeInterval { ProcessInfo.processInfo.systemUptime - startUptime }

    func start() {
        guard !isRunning else { return }
        guard motion.isDeviceMotionAvailable else {
            statusMessage = "Motion sensors unavailable on this device."
            return
        }

        location.requestWhenInUseAuthorization()
        UNUserNotificationCenter.current().requestAuthorization(options: [.alert, .sound]) { _, _ in }

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
        elapsed = 0
        crashAlert = false
        lastLocation = nil
        startUptime = ProcessInfo.processInfo.systemUptime
        startDate = Date()
        isRunning = true
        statusMessage = "Recording ride…"

        // Keep the app alive in the background via an active location session.
        location.allowsBackgroundLocationUpdates = true
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
        }
    }

    func stop() {
        guard isRunning else { return }
        isRunning = false
        motion.stopDeviceMotionUpdates()
        altimeter.stopRelativeAltitudeUpdates()
        location.stopUpdatingLocation()
        location.allowsBackgroundLocationUpdates = false
        timer?.invalidate()
        timer = nil

        if let summary = aggregator.finish() {
            motionSummaries.append(summary)
        }

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
    func locationManager(_ manager: CLLocationManager, didUpdateLocations locations: [CLLocation]) {
        for loc in locations {
            if let previous = lastLocation {
                let step = loc.distance(from: previous)
                if step.isFinite, step < 500 { // ignore obvious GPS jumps
                    distanceMeters += step
                }
            }
            lastLocation = loc
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
    }

    func locationManager(_ manager: CLLocationManager, didFailWithError error: Error) {}
}
