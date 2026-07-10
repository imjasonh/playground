import Foundation
import CoreLocation

/// Configuration for a Follow the Hum hunt.
struct HumHuntConfig: Equatable {
    /// Closest the hidden spot may be when the hunt starts.
    var minHideDistanceMeters: Double = 120
    /// Farthest the hidden spot may be when the hunt starts.
    var maxHideDistanceMeters: Double = 320
    /// Arrive within this radius to win.
    var findRadiusMeters: Double = 22
    /// Soften the hum when the target is behind the listener.
    var rearAttenuation: Double = 0.35
}

/// Continuous audio parameters derived from where the listener is facing and
/// how far they are from the hidden spot. The audio engine maps these to a
/// spatial sine hum — no map arrow required.
struct HumAudioParams: Equatable {
    /// Stereo / spatial pan in [-1, 1] (left … right). 0 = centered ahead.
    var pan: Double
    /// Linear gain in [0, 1].
    var volume: Double
    /// Hum fundamental in Hz. Creeps up as you get closer.
    var frequencyHz: Double
    /// 0 = clear, 1 = muffled (low-pass). Higher when facing away.
    var muffling: Double
    /// How "present" the hum feels; used for subtle vibrato depth.
    var presence: Double
}

/// Snapshot of an in-progress (or finished) hunt for the UI.
struct HumHuntSnapshot: Equatable {
    var phase: HumGame.Phase
    var distanceMeters: Double?
    var relativeBearingDegrees: Double?
    var audio: HumAudioParams?
    var statusMessage: String
}

/// Pure state machine for Follow the Hum. Feed it location + heading; it
/// hides a spot, scores steering, and decides when you've found it.
final class HumGame {
    enum Phase: Equatable {
        case idle
        case hunting
        case found
    }

    let config: HumHuntConfig

    private(set) var phase: Phase = .idle
    private(set) var hiddenCoordinate: CLLocationCoordinate2D?
    private(set) var lastDistanceMeters: Double?
    private(set) var lastRelativeBearingDegrees: Double?
    private(set) var lastAudio: HumAudioParams?

    init(config: HumHuntConfig = HumHuntConfig()) {
        self.config = config
    }

    /// Begin a hunt by hiding a spot near `origin`. Returns false if already hunting.
    @discardableResult
    func startHunt(
        from origin: CLLocationCoordinate2D,
        randomBearing: @escaping () -> Double = { Double.random(in: 0..<360) },
        randomUnit: @escaping () -> Double = { Double.random(in: 0...1) }
    ) -> Bool {
        guard phase != .hunting else { return false }
        hiddenCoordinate = HumGeo.hideSpot(
            from: origin,
            minDistanceMeters: config.minHideDistanceMeters,
            maxDistanceMeters: config.maxHideDistanceMeters,
            randomBearing: randomBearing,
            randomUnit: randomUnit
        )
        phase = .hunting
        lastDistanceMeters = nil
        lastRelativeBearingDegrees = nil
        lastAudio = nil
        return true
    }

    func stop() {
        phase = .idle
        hiddenCoordinate = nil
        lastDistanceMeters = nil
        lastRelativeBearingDegrees = nil
        lastAudio = nil
    }

    /// Update with the listener's position and true heading (degrees from north).
    /// Returns a UI snapshot; when distance ≤ find radius, phase becomes `.found`.
    @discardableResult
    func update(location: CLLocationCoordinate2D, headingDegrees: Double) -> HumHuntSnapshot {
        guard phase == .hunting || phase == .found, let target = hiddenCoordinate else {
            return HumHuntSnapshot(
                phase: .idle,
                distanceMeters: nil,
                relativeBearingDegrees: nil,
                audio: nil,
                statusMessage: "Start a hunt to hide a nearby spot."
            )
        }

        let distance = HumGeo.distanceMeters(from: location, to: target)
        let bearing = HumGeo.bearingDegrees(from: location, to: target)
        let relative = HumGeo.relativeBearingDegrees(targetBearing: bearing, heading: headingDegrees)
        let audio = Self.audioParams(
            relativeBearingDegrees: relative,
            distanceMeters: distance,
            config: config
        )

        lastDistanceMeters = distance
        lastRelativeBearingDegrees = relative
        lastAudio = audio

        if phase == .hunting, distance <= config.findRadiusMeters {
            phase = .found
        }

        return HumHuntSnapshot(
            phase: phase,
            distanceMeters: distance,
            relativeBearingDegrees: relative,
            audio: audio,
            statusMessage: statusMessage(phase: phase, distance: distance, relative: relative)
        )
    }

    /// Map steering error + distance → a pleasant spatial hum.
    static func audioParams(
        relativeBearingDegrees: Double,
        distanceMeters: Double,
        config: HumHuntConfig
    ) -> HumAudioParams {
        let relative = HumGeo.normalizeAngleDegrees(relativeBearingDegrees)
        let radians = relative * .pi / 180

        // Ahead → pan 0; right ear → +1; left → -1.
        let pan = sin(radians)

        // Front hemisphere is clear; behind the head softens.
        let frontness = max(0, cos(radians)) // 1 ahead, 0 at sides, -1 behind → clamped
        let rearFactor = config.rearAttenuation + (1 - config.rearAttenuation) * frontness

        // Closer = louder. Cap so the start of a long hunt isn't silent.
        let near = max(0, min(1, 1 - (distanceMeters / max(config.maxHideDistanceMeters * 1.4, 1))))
        let volume = max(0.12, min(1, (0.22 + 0.78 * near) * rearFactor))

        // Warm low hum that brightens as you approach.
        let frequencyHz = 168 + 72 * near

        // Facing away muffles; facing the target opens the filter.
        let muffling = max(0, min(1, (1 - frontness) * 0.85))

        let presence = max(0, min(1, frontness * (0.35 + 0.65 * near)))

        return HumAudioParams(
            pan: pan,
            volume: volume,
            frequencyHz: frequencyHz,
            muffling: muffling,
            presence: presence
        )
    }

    private func statusMessage(phase: Phase, distance: Double, relative: Double) -> String {
        switch phase {
        case .idle:
            return "Start a hunt to hide a nearby spot."
        case .found:
            return "You found it — the hum led you home."
        case .hunting:
            let absRel = abs(relative)
            if distance < config.findRadiusMeters * 2.5 {
                return "The hum is almost underfoot…"
            }
            if absRel < 25 {
                return "Centered — walk toward the hum."
            }
            if absRel < 70 {
                return relative > 0 ? "Drift right — follow the hum." : "Drift left — follow the hum."
            }
            if absRel < 120 {
                return "Turn toward the warmer side."
            }
            return "It's behind you — turn around slowly."
        }
    }
}
