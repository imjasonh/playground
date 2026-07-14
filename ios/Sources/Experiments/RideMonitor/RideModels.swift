import Foundation

/// One GPS fix logged during a ride. `t` is seconds since the ride started.
/// `speed`/`course` are -1 when Core Location can't determine them.
struct LocationSample: Codable {
    let t: TimeInterval
    let latitude: Double
    let longitude: Double
    let altitude: Double
    let horizontalAccuracy: Double
    let verticalAccuracy: Double
    let speed: Double
    let course: Double
}

/// Per-second aggregate of the high-rate accelerometer/gyro stream (we don't
/// persist every 50 Hz sample — this keeps saved rides small but browsable).
struct MotionSummary: Codable {
    let t: TimeInterval
    let peakG: Double
    let meanG: Double
    let peakRotation: Double // rad/s magnitude
    let samples: Int
}

/// A barometric altimeter reading (relative altitude vs. ride start + pressure).
struct AltitudeSample: Codable {
    let t: TimeInterval
    let relativeAltitude: Double // meters
    let pressureKPa: Double
}

/// A complete, saved ride. Persisted as JSON by `RideStore`.
struct Ride: Codable, Identifiable {
    let id: UUID
    let startedAt: Date
    let endedAt: Date
    let durationSeconds: TimeInterval
    let distanceMeters: Double
    let peakG: Double
    let joltCount: Int
    let crashCount: Int
    /// Short on-device label (a few words), filled after the ride ends.
    /// Optional so older saved JSON files still decode.
    var summary: String? = nil
    /// Watch HealthKit stats mirrored during the ride (nil when no Watch /
    /// no authorization / no samples). Optional for older saved files.
    var averageHeartRateBPM: Double? = nil
    var maxHeartRateBPM: Double? = nil
    var activeEnergyKilocalories: Double? = nil
    var events: [RideEvent]
    var track: [LocationSample]
    var motion: [MotionSummary]
    var barometer: [AltitudeSample]

    /// Net elevation change from the barometer, in meters, if available.
    var elevationGain: Double? {
        guard let first = barometer.first?.relativeAltitude,
              let last = barometer.last?.relativeAltitude else { return nil }
        return last - first
    }

    /// Max recorded speed in m/s across the track (ignoring invalid readings).
    var maxSpeed: Double {
        track.map(\.speed).filter { $0 >= 0 }.max() ?? 0
    }
}
