import Foundation

/// `ProcessInfo.ThermalState` cases the Live Activity and experiment UI share.
///
/// Kept as our own type so unit tests and the WidgetKit extension can map
/// icons and copy without importing UIKit.
enum ThermalLevel: String, Codable, Hashable, CaseIterable {
    case nominal
    case fair
    case serious
    case critical

    /// Live Activity is only requested for a non-nominal state.
    var showsLiveActivity: Bool { self != .nominal }

    var title: String {
        switch self {
        case .nominal: return "Nominal"
        case .fair: return "Fair"
        case .serious: return "Serious"
        case .critical: return "Critical"
        }
    }

    /// SF Symbol that changes with the state so color is not the only signal.
    var symbolName: String {
        switch self {
        case .nominal: return "thermometer"
        case .fair: return "thermometer.medium"
        case .serious: return "thermometer.high"
        case .critical: return "thermometer.sun.fill"
        }
    }

    /// Spoken name for the Dynamic Island glyph and the experiment header.
    var accessibilityLabel: String {
        "Thermal state \(title)"
    }

    /// What the system does at this level, from `ProcessInfo.ThermalState`.
    var detail: String {
        switch self {
        case .nominal:
            return "The thermal state is within normal limits. The system is not reducing performance for heat."
        case .fair:
            return "The thermal state is slightly elevated. The system may start reducing CPU and GPU performance."
        case .serious:
            return "The thermal state is high. The system is reducing performance to shed heat."
        case .critical:
            return "The thermal state is significantly affecting performance. The system reduces work further."
        }
    }

    init(_ state: ProcessInfo.ThermalState) {
        switch state {
        case .nominal:
            self = .nominal
        case .fair:
            self = .fair
        case .serious:
            self = .serious
        case .critical:
            self = .critical
        @unknown default:
            // A future hotter-than-critical case should still show the island.
            self = .critical
        }
    }
}

/// Deep link target shared by the Live Activity and the host experiment.
enum ThermalLink {
    static let experimentID = "thermal"
}
