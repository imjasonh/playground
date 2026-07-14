import Foundation

/// How hard a jolt was, in rough increasing severity.
enum RideSeverity: String, CaseIterable, Codable {
    /// No longer recorded — the classifier's floor starts at `pothole`.
    /// Kept only so rides saved by older builds still decode and display.
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
    let id: UUID
    let severity: RideSeverity
    /// Peak acceleration magnitude (gravity removed), in g.
    let peakG: Double
    /// Seconds since the start of the ride.
    let at: TimeInterval
    var latitude: Double?
    var longitude: Double?

    init(
        id: UUID = UUID(),
        severity: RideSeverity,
        peakG: Double,
        at: TimeInterval,
        latitude: Double? = nil,
        longitude: Double? = nil
    ) {
        self.id = id
        self.severity = severity
        self.peakG = peakG
        self.at = at
        self.latitude = latitude
        self.longitude = longitude
    }
}
