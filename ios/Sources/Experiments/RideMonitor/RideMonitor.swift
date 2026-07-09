import Foundation
import CoreMotion
import CoreLocation
import UserNotifications
#if canImport(UIKit)
import UIKit
#endif

/// Orchestrates a ride session: high-rate motion sampling for jolt/crash
/// detection plus a background location session that keeps the app alive with
/// the screen locked. All the interesting decision logic lives in the pure
/// `RideEventClassifier`; this type just wires up the device APIs and publishes
/// state for the view.
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

    private let motion = CMMotionManager()
    private let location = CLLocationManager()
    private var classifier = RideEventClassifier()

    private var startUptime: TimeInterval = 0
    private var timer: Timer?
    private var lastLocation: CLLocation?

    private let sampleHz = 50.0

    override init() {
        super.init()
        location.delegate = self
        location.desiredAccuracy = kCLLocationAccuracyBest
        location.activityType = .fitness
    }

    func start() {
        guard !isRunning else { return }
        guard motion.isDeviceMotionAvailable else {
            statusMessage = "Motion sensors unavailable on this device."
            return
        }

        location.requestWhenInUseAuthorization()
        UNUserNotificationCenter.current().requestAuthorization(options: [.alert, .sound]) { _, _ in }

        classifier = RideEventClassifier()
        events = []
        joltCount = 0
        peakG = 0
        currentG = 0
        distanceMeters = 0
        elapsed = 0
        crashAlert = false
        lastLocation = nil
        startUptime = ProcessInfo.processInfo.systemUptime
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

        timer = Timer.scheduledTimer(withTimeInterval: 0.25, repeats: true) { [weak self] _ in
            guard let self, self.isRunning else { return }
            self.elapsed = ProcessInfo.processInfo.systemUptime - self.startUptime
        }
    }

    func stop() {
        guard isRunning else { return }
        isRunning = false
        motion.stopDeviceMotionUpdates()
        location.stopUpdatingLocation()
        location.allowsBackgroundLocationUpdates = false
        timer?.invalidate()
        timer = nil
        statusMessage = "Ride ended — \(events.count) event(s)."
    }

    func dismissCrashAlert() {
        crashAlert = false
    }

    private func ingest(_ data: CMDeviceMotion) {
        let a = data.userAcceleration // gravity already removed, in g
        let magnitude = (a.x * a.x + a.y * a.y + a.z * a.z).squareRoot()
        currentG = magnitude
        peakG = max(peakG, magnitude)

        let t = ProcessInfo.processInfo.systemUptime - startUptime
        for var event in classifier.process(magnitude: magnitude, at: t) {
            event.latitude = lastLocation?.coordinate.latitude
            event.longitude = lastLocation?.coordinate.longitude
            events.insert(event, at: 0)
            if event.severity == .crash {
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
        }
    }

    func locationManager(_ manager: CLLocationManager, didFailWithError error: Error) {}
}
