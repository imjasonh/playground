import Foundation
import SwiftUI
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Why Onramp can or cannot use on-device Foundation Models.
enum FoundationModelsStatus: Equatable, Sendable {
    case checking
    case available
    /// Supported Mac, but Apple Intelligence is off in System Settings.
    case needsAppleIntelligenceEnabled
    /// Assets downloading / warming up — keep polling.
    case modelNotReady
    /// macOS too old or FoundationModels framework missing at runtime.
    case unsupportedOperatingSystem
    /// Hardware / region will never get Apple Intelligence.
    case deviceNotEligible
    case unavailableOther(String)

    /// Permanent: do not let the user into the app.
    var isHardBlock: Bool {
        switch self {
        case .unsupportedOperatingSystem, .deviceNotEligible, .unavailableOther:
            return true
        case .checking, .available, .needsAppleIntelligenceEnabled, .modelNotReady:
            return false
        }
    }

    /// Temporary: fullscreen setup until the model is ready.
    var isSetupRequired: Bool {
        switch self {
        case .needsAppleIntelligenceEnabled, .modelNotReady:
            return true
        default:
            return false
        }
    }

    var blocksMainUI: Bool {
        isHardBlock || isSetupRequired || self == .checking
    }
}

/// Shared availability for the app gate + Chat. Polls while setup is pending.
@MainActor
final class FoundationModelsGateModel: ObservableObject {
    @Published private(set) var status: FoundationModelsStatus = .checking
    /// Session-only escape to Playbooks/Toolbox without Chat (offline install edge case).
    @Published var allowPlaybooksWithoutModel = false

    private var pollTask: Task<Void, Never>?

    init() {
        refresh()
        startPollingIfNeeded()
    }

    var showsMainApp: Bool {
        status == .available || (allowPlaybooksWithoutModel && !status.isHardBlock && status != .checking)
    }

    func refresh() {
        status = Self.evaluate()
        if status == .available {
            allowPlaybooksWithoutModel = false
        }
        startPollingIfNeeded()
    }

    func openSettingsAndRefresh() {
        AppleIntelligenceSettings.open()
        // Give Settings a beat, then re-check repeatedly.
        Task { @MainActor in
            try? await Task.sleep(nanoseconds: 1_500_000_000)
            refresh()
        }
    }

    func continueWithPlaybooksOnly() {
        guard !status.isHardBlock else { return }
        allowPlaybooksWithoutModel = true
        pollTask?.cancel()
        pollTask = nil
    }

    private func startPollingIfNeeded() {
        pollTask?.cancel()
        pollTask = nil
        guard status.isSetupRequired, !allowPlaybooksWithoutModel else { return }
        pollTask = Task { @MainActor [weak self] in
            while let self, !Task.isCancelled {
                try? await Task.sleep(nanoseconds: 3_000_000_000)
                guard !Task.isCancelled else { return }
                self.status = Self.evaluate()
                if self.status == .available {
                    self.allowPlaybooksWithoutModel = false
                    return
                }
                if self.status.isHardBlock || !self.status.isSetupRequired {
                    return
                }
            }
        }
    }

    /// Pure mapping used by tests + runtime.
    static func evaluate() -> FoundationModelsStatus {
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *) {
            return mapAvailability(SystemLanguageModel.default.availability)
        }
        #endif
        return .unsupportedOperatingSystem
    }

    #if canImport(FoundationModels)
    @available(macOS 26.0, *)
    static func mapAvailability(_ availability: SystemLanguageModel.Availability) -> FoundationModelsStatus {
        switch availability {
        case .available:
            return .available
        case .unavailable(let reason):
            return mapUnavailableReason(reason)
        @unknown default:
            return .unavailableOther("Apple Intelligence reported an unknown availability state.")
        }
    }

    @available(macOS 26.0, *)
    static func mapUnavailableReason(_ reason: SystemLanguageModel.Availability.UnavailableReason)
        -> FoundationModelsStatus
    {
        switch reason {
        case .deviceNotEligible:
            return .deviceNotEligible
        case .appleIntelligenceNotEnabled:
            return .needsAppleIntelligenceEnabled
        case .modelNotReady:
            return .modelNotReady
        @unknown default:
            // Keep resilient across SDK refinements — prefer setup nudge over hard block
            // when we can't classify, unless the description clearly says ineligible.
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
