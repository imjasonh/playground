import Combine
import CoreLocation
import Foundation

/// Owns location/heading permissions, the pure `HumGame`, and the hum audio
/// engine. The SwiftUI view observes this object.
final class HumHuntSession: NSObject, ObservableObject {
    @Published private(set) var phase: HumGame.Phase = .idle
    @Published private(set) var statusMessage = "Put on AirPods, then start a hunt."
    @Published private(set) var distanceMeters: Double?
    @Published private(set) var relativeBearingDegrees: Double?
    @Published private(set) var authorizationDenied = false
    @Published private(set) var headingAvailable = true
    @Published private(set) var lastCoordinate: CLLocationCoordinate2D?
    @Published private(set) var lastHeadingDegrees: Double?

    private let game = HumGame()
    private let locationManager = CLLocationManager()
    private let audio = HumAudioEngine()
    private var wantsHunt = false

    override init() {
        super.init()
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
        locationManager.stopUpdatingLocation()
        locationManager.stopUpdatingHeading()
        phase = .idle
        distanceMeters = nil
        relativeBearingDegrees = nil
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

        if let coordinate = lastCoordinate {
            startHuntIfNeeded(from: coordinate)
        } else {
            statusMessage = "Finding your location…"
        }
    }

    private func startHuntIfNeeded(from coordinate: CLLocationCoordinate2D) {
        guard wantsHunt, phase != .hunting else { return }
        // Prefer a real heading before hiding the spot so the first hum pan is meaningful.
        guard lastHeadingDegrees != nil else {
            statusMessage = "Calibrating compass — walk a few steps in a figure‑eight if needed…"
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
        publish(game.update(location: coordinate, headingDegrees: lastHeadingDegrees ?? 0))
    }

    private func publish(_ snapshot: HumHuntSnapshot) {
        phase = snapshot.phase
        distanceMeters = snapshot.distanceMeters
        relativeBearingDegrees = snapshot.relativeBearingDegrees
        statusMessage = snapshot.statusMessage

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
            locationManager.stopUpdatingLocation()
            locationManager.stopUpdatingHeading()
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
        // Ignore very coarse fixes for hiding / winning.
        guard location.horizontalAccuracy <= 40 else { return }

        lastCoordinate = location.coordinate
        if wantsHunt, phase == .idle || phase == .found {
            startHuntIfNeeded(from: location.coordinate)
        } else if phase == .hunting, let heading = lastHeadingDegrees {
            publish(game.update(location: location.coordinate, headingDegrees: heading))
        }
    }

    func locationManager(_ manager: CLLocationManager, didUpdateHeading newHeading: CLHeading) {
        let trueHeading = newHeading.trueHeading >= 0 ? newHeading.trueHeading : newHeading.magneticHeading
        guard trueHeading >= 0 else { return }
        lastHeadingDegrees = trueHeading
        if wantsHunt, (phase == .idle || phase == .found), let coordinate = lastCoordinate {
            startHuntIfNeeded(from: coordinate)
            return
        }
        guard phase == .hunting, let coordinate = lastCoordinate else { return }
        publish(game.update(location: coordinate, headingDegrees: trueHeading))
    }

    func locationManager(_ manager: CLLocationManager, didFailWithError error: Error) {
        statusMessage = "Location error: \(error.localizedDescription)"
    }
}
