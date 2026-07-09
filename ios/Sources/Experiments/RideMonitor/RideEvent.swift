import Foundation

/// How hard a jolt was, in rough increasing severity.
enum RideSeverity: String, CaseIterable, Codable {
    case shake
    case pothole
    case impact
    case crash

    var title: String {
        switch self {
        case .shake: return "Shake"
        case .pothole: return "Pothole"
        case .impact: return "Hard impact"
        case .crash: return "Possible crash"
        }
    }

    /// SF Symbol used in the UI.
    var icon: String {
        switch self {
        case .shake: return "waveform.path"
        case .pothole: return "road.lanes"
        case .impact: return "exclamationmark.triangle"
        case .crash: return "sos"
        }
    }
}

/// A detected motion event during a ride. The detection core fills `severity`,
/// `peakG`, and `at`; the session manager attaches the location afterwards.
struct RideEvent: Identifiable, Codable {
    let id = UUID()
    let severity: RideSeverity
    /// Peak acceleration magnitude (gravity removed), in g.
    let peakG: Double
    /// Seconds since the start of the ride.
    let at: TimeInterval
    var latitude: Double?
    var longitude: Double?
}
