import AppKit
import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Soft availability state for Apple's on-device Foundation Models.
/// Unlike Onramp, Lantern NEVER blocks the user when AFM is unavailable —
/// all collectors, anomaly rules, and deterministic explanations work without it.
enum FoundationModelsAvailability: Equatable, Sendable {
    case available
    case needsAppleIntelligenceEnabled
    case modelNotReady
    case unsupportedOperatingSystem
    case deviceNotEligible
    case unavailableOther(String)

    var isAvailable: Bool {
        self == .available
    }

    var shortLabel: String {
        switch self {
        case .available:
            return "Apple Intelligence ready"
        case .needsAppleIntelligenceEnabled:
            return "Apple Intelligence off (using built-in explanations)"
        case .modelNotReady:
            return "On-device model downloading (using built-in explanations)"
        case .unsupportedOperatingSystem:
            return "macOS 26+ needed for AI explanations (built-in active)"
        case .deviceNotEligible:
            return "Mac not eligible for Apple Intelligence (built-in active)"
        case .unavailableOther(let detail):
            return "AI unavailable: \(detail)"
        }
    }

    static func evaluate() -> FoundationModelsAvailability {
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *) {
            return mapAvailability(SystemLanguageModel.default.availability)
        }
        #endif
        return .unsupportedOperatingSystem
    }

    #if canImport(FoundationModels)
    @available(macOS 26.0, *)
    static func mapAvailability(
        _ availability: SystemLanguageModel.Availability
    ) -> FoundationModelsAvailability {
        switch availability {
        case .available:
            return .available
        case .unavailable(let reason):
            return mapUnavailableReason(reason)
        @unknown default:
            return .unavailableOther("Unknown availability state")
        }
    }

    @available(macOS 26.0, *)
    static func mapUnavailableReason(
        _ reason: SystemLanguageModel.Availability.UnavailableReason
    ) -> FoundationModelsAvailability {
        switch reason {
        case .deviceNotEligible:
            return .deviceNotEligible
        case .appleIntelligenceNotEnabled:
            return .needsAppleIntelligenceEnabled
        case .modelNotReady:
            return .modelNotReady
        @unknown default:
            let text = String(describing: reason).lowercased()
            if text.contains("eligible") || text.contains("unsupported") {
                return .deviceNotEligible
            }
            if text.contains("ready") || text.contains("download") {
                return .modelNotReady
            }
            if text.contains("enabled") || text.contains("intelligence") {
                return .needsAppleIntelligenceEnabled
            }
            return .unavailableOther(String(describing: reason))
        }
    }
    #endif
}

enum AppleIntelligenceSettings {
    static func open() {
        let candidates = [
            "x-apple.systempreferences:com.apple.Siri-Settings.extension",
            "x-apple.systempreferences:com.apple.preference.security",
        ]
        for raw in candidates {
            if let url = URL(string: raw), NSWorkspace.shared.open(url) {
                return
            }
        }
    }
}
