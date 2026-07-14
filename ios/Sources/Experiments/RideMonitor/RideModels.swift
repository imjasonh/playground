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

/// Why a ride recording ended. Persisted so a mid-ride stop can be diagnosed
/// from the saved JSON / JSONL export without Console logs.
enum RideEndReason: String, Codable, Equatable, CaseIterable {
    case userStopped
    case sensingGap
    case locationLimitedToWhenInUse
    case locationDenied
    case backgroundWithoutAlways
    case alwaysRequiredOnForeground

    var displayName: String {
        switch self {
        case .userStopped:
            return "Stopped by user"
        case .sensingGap:
            return "Sensing paused (keep-alive lost)"
        case .locationLimitedToWhenInUse:
            return "Location limited to While Using"
        case .locationDenied:
            return "Location permission denied"
        case .backgroundWithoutAlways:
            return "Left app without Always location"
        case .alwaysRequiredOnForeground:
            return "Always location required on return"
        }
    }
}

/// Forensic counters captured at stop. Optional on older saved rides.
struct RideRecordingDiagnostics: Codable, Equatable {
    var endReason: RideEndReason
    /// Human-readable detail (also shown in the in-app status line).
    var endDetail: String? = nil
    /// Uptime offset of the last motion sample before stop.
    var lastMotionOffset: TimeInterval? = nil
    /// Uptime offset of the last GPS sample before stop.
    var lastLocationOffset: TimeInterval? = nil
    /// How many times Core Motion was restarted after a stall.
    var motionRestartCount: Int = 0
    /// Core Location `didFailWithError` count during the ride.
    var locationErrorCount: Int = 0
    /// Slowest Live Activity / Watch companion push observed (ms).
    var maxCompanionPushMilliseconds: Double? = nil
    /// `CLAuthorizationStatus` description at stop.
    var authorizationStatusAtEnd: String? = nil
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
    var basalEnergyKilocalories: Double? = nil
    /// Watch GPS cycling distance (meters); phone `distanceMeters` remains primary.
    var watchDistanceMeters: Double? = nil
    var averageCadenceRPM: Double? = nil
    var averageCyclingPowerWatts: Double? = nil
    var maxCyclingPowerWatts: Double? = nil
    /// Why / how recording ended, plus counters useful for debugging stops.
    var recordingDiagnostics: RideRecordingDiagnostics? = nil
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
