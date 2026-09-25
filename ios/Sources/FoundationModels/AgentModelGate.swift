import UIKit

/// Why Foundation Models is or isn't usable on this device.
enum AgentModelGate: Equatable {
    case available
    case needsAppleIntelligence
    case modelNotReady
    case deviceNotEligible
    case other(String)

    var isAvailable: Bool {
        if case .available = self { return true }
        return false
    }

    var title: String {
        switch self {
        case .available:
            return "On-device Foundation Model ready"
        case .needsAppleIntelligence:
            return "Turn on Apple Intelligence"
        case .modelNotReady:
            return "Model still downloading"
        case .deviceNotEligible:
            return "Device not eligible"
        case .other:
            return "Apple Intelligence unavailable"
        }
    }

    var detail: String {
        switch self {
        case .available:
            return "On-device Foundation Model ready"
        case .needsAppleIntelligence:
            return "Turn on Apple Intelligence in Settings, then come back."
        case .modelNotReady:
            return "Apple Intelligence is on, but the on-device model is still downloading. Keep Wi-Fi and power connected, then check again."
        case .deviceNotEligible:
            return "This hardware doesn't support Apple Intelligence."
        case .other(let reason):
            return reason
        }
    }

    /// Single primary button for the unavailable pane, when one helps.
    var primaryAction: AgentModelGateAction? {
        switch self {
        case .needsAppleIntelligence:
            return .openAppleIntelligenceSettings
        case .modelNotReady:
            return .checkAgain
        case .available, .deviceNotEligible, .other:
            return nil
        }
    }
}

enum AgentModelGateAction: Equatable {
    case openAppleIntelligenceSettings
    case checkAgain

    var title: String {
        switch self {
        case .openAppleIntelligenceSettings:
            return "Open Apple Intelligence Settings"
        case .checkAgain:
            return "Check again"
        }
    }
}

/// Opens Settings as close to Apple Intelligence & Siri as the system allows.
@MainActor
enum AgentAppleIntelligenceSettings {
    static func open() async {
        // Undocumented Settings deep links. Try the Siri / Apple Intelligence pane first,
        // then Settings root, then this app's Settings page.
        let candidates: [URL] = [
            URL(string: "App-prefs:root=SIRI"),
            URL(string: "prefs:root=SIRI"),
            URL(string: "App-prefs:"),
            URL(string: UIApplication.openSettingsURLString),
        ].compactMap { $0 }

        for url in candidates {
            if await UIApplication.shared.open(url) {
                return
            }
        }
    }
}
