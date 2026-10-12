import Foundation

/// `ProcessInfo.ThermalState` mapped for the Live Activity and experiment UI.
enum ThermalLevel: String, Codable, Hashable, CaseIterable {
    case nominal
    case fair
    case serious
    case critical

    var showsLiveActivity: Bool { self != .nominal }

    var title: String {
        switch self {
        case .nominal: return "Nominal"
        case .fair: return "Fair"
        case .serious: return "Serious"
        case .critical: return "Critical"
        }
    }

    var symbolName: String {
        switch self {
        case .nominal: return "thermometer"
        case .fair: return "thermometer.medium"
        case .serious: return "thermometer.high"
        case .critical: return "thermometer.sun.fill"
        }
    }

    var accessibilityLabel: String {
        "Thermal state \(title)"
    }

    var detail: String {
        switch self {
        case .nominal:
            return "The thermal state is within normal limits. The system is not reducing performance for heat."
        case .fair:
            return "The thermal state is slightly elevated. The system may start reducing CPU and GPU performance."
        case .serious:
            return "The thermal state is high. The system is reducing performance because the device is hot."
        case .critical:
            return "The thermal state is high enough that the system reduces work further."
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
            // A newer thermal case still shows the island.
            self = .critical
        }
    }
}

enum ThermalLink {
    static let experimentID = "thermal"
}
