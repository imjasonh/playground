import Combine
import CoreLocation
import CoreMotion
import Foundation

/// Owns location/heading permissions, AirPods head tracking, the pure `HumGame`,
/// and the hum audio engine. The SwiftUI view observes this object.
///
/// Steering uses **head** facing when AirPods motion is available: we lock
/// headphone yaw to true north once via the phone compass at hunt start, then
/// the phone can go in a pocket while the hum follows your head.
final class HumHuntSession: NSObject, ObservableObject {
    @Published private(set) var phase: HumGame.Phase = .idle
    @Published private(set) var statusMessage = "Put on AirPods, then start a hunt."
    @Published private(set) var distanceMeters: Double?
    @Published private(set) var relativeBearingDegrees: Double?
    @Published private(set) var authorizationDenied = false
    @Published private(set) var headingAvailable = true
    @Published private(set) var usingHeadTracking = false
    @Published private(set) var lastCoordinate: CLLocationCoordinate2D?
    @Published private(set) var lastHeadingDegrees: Double?

    private let game = HumGame()
    private let locationManager = CLLocationManager()
    private let headphoneMotion = CMHeadphoneMotionManager()
    private let motionQueue = OperationQueue()
    private let audio = HumAudioEngine()
    private var fusion = HumHeadingFusion()
    private var wantsHunt = false

    override init() {
        super.init()
        motionQueue.name = "FollowTheHum.headMotion"
        motionQueue.maxConcurrentOperationCount = 1
        locationManager.delegate = self
        locationManager.desiredAccuracy = kCLLocationAccuracyBest
        locationManager.activityType = .fitness
        locationManager.headingFilter = 2
        headingAvailable = CLLocationManager.headingAvailable()
    }

    var isHunting: Bool { phase == .hunting }
    var isFound: Bool { phase == .found }

    func requestPermissionsAndStart() {
        wantsHunt = true
        authorizationDenied = false
        fusion.reset()
        usingHeadTracking = false
        switch locationManager.authorizationStatus {
        case .notDetermined:
            locationManager.requestWhenInUseAuthorization()
        case .authorizedWhenInUse, .authorizedAlways:
            beginUpdatesAndHunt()
        case .denied, .restricted:
            authorizationDenied = true
            statusMessage = "Location access is needed to hide a nearby spot."
            wantsHunt = false
        @unknown default:
            statusMessage = "Location status unknown."
            wantsHunt = false
        }
    }

    func stop() {
        wantsHunt = false
        game.stop()
        audio.stop()
        stopSensors()
        fusion.reset()
        usingHeadTracking = false
        phase = .idle
        distanceMeters = nil
        relativeBearingDegrees = nil
        lastHeadingDegrees = nil
        statusMessage = "Hunt stopped. Start again when you're ready."
    }

    private func beginUpdatesAndHunt() {
        guard CLLocationManager.headingAvailable() else {
            headingAvailable = false
            wantsHunt = false
            statusMessage = "This device has no compass — hunting needs a real iPhone outdoors."
            return
        }
        headingAvailable = true
        locationManager.startUpdatingLocation()
        locationManager.startUpdatingHeading()
        startHeadTrackingIfAvailable()

        if let coordinate = lastCoordinate {
            startHuntIfNeeded(from: coordinate)
        } else {
            statusMessage = "Finding your location…"
        }
    }

    private func startHeadTrackingIfAvailable() {
        guard headphoneMotion.isDeviceMotionAvailable else {
            // Still playable with phone compass (hold the phone facing forward).
            return
        }
        headphoneMotion.startDeviceMotionUpdates(to: motionQueue) { [weak self] motion, error in
            guard let self else { return }
            if error != nil { return }
            guard let motion else { return }
            // CMAttitude.yaw is radians; convert. Same axis used for left/right turns.
            let yawDegrees = motion.attitude.yaw * 180 / .pi
            DispatchQueue.main.async {
                self.fusion.ingestHeadYaw(yawDegrees)
                self.usingHeadTracking = self.fusion.isHeadLocked
                self.tickFromSensors()
            }
        }
    }

    private func stopSensors() {
        locationManager.stopUpdatingLocation()
        locationManager.stopUpdatingHeading()
        if headphoneMotion.isDeviceMotionActive {
            headphoneMotion.stopDeviceMotionUpdates()
        }
    }

    private func startHuntIfNeeded(from coordinate: CLLocationCoordinate2D) {
        guard wantsHunt, phase != .hunting else { return }
        guard let facing = fusion.facingDegrees() else {
            if headphoneMotion.isDeviceMotionAvailable, fusion.lastHeadYawDegrees == nil {
                statusMessage = "Waiting for AirPods head tracking — keep them in your ears…"
            } else {
                statusMessage = "Calibrating compass — hold the phone in front of you, face forward…"
            }
            return
        }
        // If AirPods are connected, wait for the yaw↔compass lock so pocket play works.
        if headphoneMotion.isDeviceMotionAvailable, !fusion.isHeadLocked {
            statusMessage = "Locking hum to your head — hold the phone facing the same way you're looking…"
            return
        }

        do {
            try audio.start()
        } catch {
            statusMessage = "Couldn't start audio: \(error.localizedDescription)"
            wantsHunt = false
            return
        }
        _ = game.startHunt(from: coordinate)
        lastHeadingDegrees = facing
        usingHeadTracking = fusion.isHeadLocked
        publish(game.update(location: coordinate, headingDegrees: facing))
    }

    private func tickFromSensors() {
        guard wantsHunt else { return }
        guard let coordinate = lastCoordinate else { return }

        if phase == .idle || phase == .found {
            startHuntIfNeeded(from: coordinate)
            return
        }
        guard phase == .hunting, let facing = fusion.facingDegrees() else { return }
        lastHeadingDegrees = facing
        usingHeadTracking = fusion.activeSource() == .airPodsHead
        publish(game.update(location: coordinate, headingDegrees: facing))
    }

    private func publish(_ snapshot: HumHuntSnapshot) {
        phase = snapshot.phase
        distanceMeters = snapshot.distanceMeters
        relativeBearingDegrees = snapshot.relativeBearingDegrees

        if snapshot.phase == .hunting, usingHeadTracking {
            statusMessage = snapshot.statusMessage
        } else if snapshot.phase == .hunting {
            statusMessage = snapshot.statusMessage + " (phone compass — AirPods head tracking unavailable)"
        } else {
            statusMessage = snapshot.statusMessage
        }

        if let audioParams = snapshot.audio, snapshot.phase == .hunting {
            audio.apply(audioParams)
        }

        if snapshot.phase == .found {
            if var celebration = snapshot.audio {
                celebration.volume = min(1, celebration.volume + 0.25)
                celebration.muffling = 0
                celebration.frequencyHz += 40
                audio.apply(celebration)
            }
            DispatchQueue.main.asyncAfter(deadline: .now() + 1.6) { [weak self] in
                self?.audio.stop()
            }
            stopSensors()
            wantsHunt = false
        }
    }
}

extension HumHuntSession: CLLocationManagerDelegate {
    func locationManagerDidChangeAuthorization(_ manager: CLLocationManager) {
        switch manager.authorizationStatus {
        case .authorizedWhenInUse, .authorizedAlways:
            if wantsHunt { beginUpdatesAndHunt() }
        case .denied, .restricted:
            authorizationDenied = true
            wantsHunt = false
            statusMessage = "Location access is needed to hide a nearby spot."
        default:
            break
        }
    }

    func locationManager(_ manager: CLLocationManager, didUpdateLocations locations: [CLLocation]) {
        guard let location = locations.last, location.horizontalAccuracy >= 0 else { return }
        guard location.horizontalAccuracy <= 40 else { return }

        lastCoordinate = location.coordinate
        tickFromSensors()
    }

    func locationManager(_ manager: CLLocationManager, didUpdateHeading newHeading: CLHeading) {
        let trueHeading = newHeading.trueHeading >= 0 ? newHeading.trueHeading : newHeading.magneticHeading
        guard trueHeading >= 0 else { return }
        // Only use phone compass to establish (or refresh before lock) world offset.
        // After AirPods are locked, ignore pocketed-phone compass noise.
        if !fusion.isHeadLocked {
            fusion.ingestPhoneHeading(trueHeading)
        }
        tickFromSensors()
    }

    func locationManager(_ manager: CLLocationManager, didFailWithError error: Error) {
        statusMessage = "Location error: \(error.localizedDescription)"
    }
}
