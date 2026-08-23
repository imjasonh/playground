import Foundation
import UIKit

/// How a run was started.
enum AgentRunSource: String, Codable, Equatable {
    case chat
    case shortcut
    case deepLink
    case share
}

/// Capability profile for the session (which tool groups are enabled).
enum AgentMode: String, CaseIterable, Identifiable, Codable {
    case observe
    case act
    case browse

    var id: String { rawValue }

    var title: String {
        switch self {
        case .observe: return "Observe"
        case .act: return "Act"
        case .browse: return "Browse"
        }
    }

    var detail: String {
        switch self {
        case .observe: return "Read-only tools (no drafts or calendar writes)"
        case .act: return "Calendar / SMS / Mail drafts with confirm"
        case .browse: return "Same as Observe; prefer in-app browser"
        }
    }
}

/// One line in the on-screen transcript.
struct AgentTranscriptEntry: Identifiable, Equatable {
    enum Kind: Equatable {
        case user
        case assistant
        case toolCall(name: String)
        case toolResult(name: String)
        case system
        case permission(domain: String)
        case confirmation(summary: String)
    }

    let id: UUID
    let date: Date
    let kind: Kind
    /// Short text shown in the chat UI.
    let text: String
    /// Full tool args / results (and similar) for JSON export only.
    let debugDetail: String?

    init(
        id: UUID = UUID(),
        date: Date = Date(),
        kind: Kind,
        text: String,
        debugDetail: String? = nil
    ) {
        self.id = id
        self.date = date
        self.kind = kind
        self.text = text
        self.debugDetail = debugDetail
    }

    /// Tool results stay out of the chat; full payloads live in the dump.
    var isVisibleInChat: Bool {
        switch kind {
        case .toolResult:
            return false
        default:
            return true
        }
    }

    var toolName: String? {
        switch kind {
        case .toolCall(let name), .toolResult(let name):
            return name
        default:
            return nil
        }
    }

    var kindLabel: String {
        switch kind {
        case .user: return "user"
        case .assistant: return "assistant"
        case .toolCall: return "toolCall"
        case .toolResult: return "toolResult"
        case .system: return "system"
        case .permission: return "permission"
        case .confirmation: return "confirmation"
        }
    }
}

/// Shareable debug dump of a Device Agent conversation.
struct AgentConversationDump: Codable, Equatable {
    var exportedAt: Date
    var mode: String
    var modelGate: String
    var modelAvailable: Bool
    var entries: [AgentConversationDumpEntry]
    var toolLog: [AgentConversationDumpToolLog]
}

struct AgentConversationDumpEntry: Codable, Equatable {
    var id: String
    var date: Date
    var kind: String
    var toolName: String?
    var displayText: String
    var debugDetail: String?
}

struct AgentConversationDumpToolLog: Codable, Equatable {
    var name: String
    var detail: String
}

/// File staged for the agent (Shortcuts, share handoff, or in-app picker).
struct AgentAttachment: Identifiable, Equatable, Codable {
    let id: UUID
    let filename: String
    /// Absolute path inside the app sandbox / inbox directory.
    let relativePath: String
    let utTypeIdentifier: String?
    let byteCount: Int

    init(
        id: UUID = UUID(),
        filename: String,
        relativePath: String,
        utTypeIdentifier: String?,
        byteCount: Int
    ) {
        self.id = id
        self.filename = filename
        self.relativePath = relativePath
        self.utTypeIdentifier = utTypeIdentifier
        self.byteCount = byteCount
    }
}

/// Queued work from Shortcuts, deep links, or a future share extension.
struct AgentPendingRun: Equatable, Codable {
    var id: UUID
    var prompt: String
    var source: AgentRunSource
    var mode: AgentMode
    var preferVoice: Bool
    var attachmentIDs: [UUID]
    var createdAt: Date

    init(
        id: UUID = UUID(),
        prompt: String,
        source: AgentRunSource,
        mode: AgentMode = .act,
        preferVoice: Bool = false,
        attachmentIDs: [UUID] = [],
        createdAt: Date = Date()
    ) {
        self.id = id
        self.prompt = prompt
        self.source = source
        self.mode = mode
        self.preferVoice = preferVoice
        self.attachmentIDs = attachmentIDs
        self.createdAt = createdAt
    }
}

/// Permission domains the tool router can request just-in-time.
enum AgentPermissionDomain: String, CaseIterable, Identifiable {
    case microphone
    case speech
    case contacts
    case calendars
    case location

    var id: String { rawValue }

    var title: String {
        switch self {
        case .microphone: return "Microphone"
        case .speech: return "Speech recognition"
        case .contacts: return "Contacts"
        case .calendars: return "Calendars"
        case .location: return "Location"
        }
    }

    /// Short copy shown in-app immediately before the system dialog.
    var prePrompt: String {
        switch self {
        case .microphone:
            return "Device Agent needs the microphone for voice input."
        case .speech:
            return "Device Agent turns speech into text on-device before sending a prompt."
        case .contacts:
            return "Device Agent looks up a name in Contacts only when a tool needs it."
        case .calendars:
            return "Device Agent reads or creates calendar events only when you ask."
        case .location:
            return "Device Agent uses your location only for map or “where am I” tools."
        }
    }
}

/// Why Foundation Models is or isn't usable on this device.
enum AgentModelGate: Equatable {
    case available
    case needsAppleIntelligence
    case modelNotReady
    case deviceNotEligible
    case unsupportedPlatform
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
        case .unsupportedPlatform:
            return "Needs iOS 26 +"
        case .other:
            return "Apple Intelligence unavailable"
        }
    }

    var detail: String {
        switch self {
        case .available:
            return "On-device Foundation Model ready"
        case .needsAppleIntelligence:
            return "Device Agent uses the on-device model. Turn on Apple Intelligence in Settings, then come back."
        case .modelNotReady:
            return "Apple Intelligence is on, but the on-device model is still downloading. Keep Wi‑Fi and power connected, then check again."
        case .deviceNotEligible:
            return "This hardware doesn’t support Apple Intelligence, so Device Agent can’t run here."
        case .unsupportedPlatform:
            return "Requires iOS 26+ with Apple Intelligence. This device or Simulator build cannot run Device Agent."
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
        case .available, .deviceNotEligible, .unsupportedPlatform, .other:
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
        // Undocumented Settings deep links — try SIRI / Apple Intelligence pane first,
        // then Settings root, then this app’s Settings page.
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

enum AgentToolError: Error, LocalizedError, Equatable {
    case permissionDenied(AgentPermissionDomain)
    case permissionNeeded(AgentPermissionDomain)
    case unavailable(String)
    case invalidArguments(String)
    case cancelled
    case confirmationRejected

    var errorDescription: String? {
        switch self {
        case .permissionDenied(let domain):
            return "\(domain.title) access is denied. Enable it in Settings if you want this tool."
        case .permissionNeeded(let domain):
            return "\(domain.title) access is required."
        case .unavailable(let message):
            return message
        case .invalidArguments(let message):
            return message
        case .cancelled:
            return "Cancelled."
        case .confirmationRejected:
            return "You declined the action."
        }
    }
}

/// A write the UI must confirm before the tool finishes.
struct AgentConfirmationRequest: Identifiable, Equatable {
    let id: UUID
    let title: String
    let message: String

    init(id: UUID = UUID(), title: String, message: String) {
        self.id = id
        self.title = title
        self.message = message
    }
}
