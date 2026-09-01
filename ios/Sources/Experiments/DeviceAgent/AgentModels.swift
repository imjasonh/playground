import Foundation
import UIKit

/// How a run was started.
enum AgentRunSource: String, Codable, Equatable {
    case chat
    case shortcut
    case deepLink
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
        /// Visible scrape summary from the in-app browser (bullets for the user).
        case pageFindings
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
        case .pageFindings: return "pageFindings"
        }
    }
}

/// One step in a structured browser replay (actions + scraped text, no screenshots).
struct AgentBrowserReplayEvent: Identifiable, Equatable, Codable {
    var id: UUID
    var date: Date
    var action: String
    var url: String?
    var title: String?
    var detail: String?
    var pageText: String?
    var elements: [String]?
    var headings: [String]?
    var listItems: [String]?

    init(
        id: UUID = UUID(),
        date: Date = Date(),
        action: String,
        url: String? = nil,
        title: String? = nil,
        detail: String? = nil,
        pageText: String? = nil,
        elements: [String]? = nil,
        headings: [String]? = nil,
        listItems: [String]? = nil
    ) {
        self.id = id
        self.date = date
        self.action = action
        self.url = url
        self.title = title
        self.detail = detail
        self.pageText = pageText
        self.elements = elements
        self.headings = headings
        self.listItems = listItems
    }
}

/// Shareable debug dump of a Device Agent conversation.
struct AgentConversationDump: Codable, Equatable {
    var exportedAt: Date
    /// Product surface for this dump (always `browser`).
    var mode: String
    var modelGate: String
    var modelAvailable: Bool
    var entries: [AgentConversationDumpEntry]
    var toolLog: [AgentConversationDumpToolLog]
    /// Ordered browser actions for playback / debugging (open, snapshot, click, type, back).
    var browserReplay: [AgentBrowserReplayEvent]
    /// Foundation Models page-extraction failures (inputs + error) for iteration.
    var extractionDiagnostics: [AgentPageExtractionDiagnostic]
}

/// One failed AFM page-extraction attempt. Enough to reproduce / improve prompts.
struct AgentPageExtractionDiagnostic: Codable, Equatable, Identifiable {
    var id: UUID
    var date: Date
    var errorCode: String
    var errorMessage: String
    var userQuestion: String
    var title: String
    var url: String
    var headings: [String]
    var listItems: [String]
    var pageText: String
    var prompt: String
    var modelGate: String
    var modelAvailable: Bool
    var rawSnapshotPrefix: String?
    var rawModelBullets: [String]?

    init(
        id: UUID = UUID(),
        date: Date = Date(),
        errorCode: String,
        errorMessage: String,
        userQuestion: String,
        title: String,
        url: String,
        headings: [String],
        listItems: [String],
        pageText: String,
        prompt: String,
        modelGate: String,
        modelAvailable: Bool,
        rawSnapshotPrefix: String? = nil,
        rawModelBullets: [String]? = nil
    ) {
        self.id = id
        self.date = date
        self.errorCode = errorCode
        self.errorMessage = errorMessage
        self.userQuestion = userQuestion
        self.title = title
        self.url = url
        self.headings = headings
        self.listItems = listItems
        self.pageText = pageText
        self.prompt = prompt
        self.modelGate = modelGate
        self.modelAvailable = modelAvailable
        self.rawSnapshotPrefix = rawSnapshotPrefix
        self.rawModelBullets = rawModelBullets
    }
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

/// Queued work from Shortcuts or deep links.
struct AgentPendingRun: Equatable, Codable {
    var id: UUID
    var prompt: String
    var source: AgentRunSource
    var preferVoice: Bool
    var createdAt: Date

    init(
        id: UUID = UUID(),
        prompt: String,
        source: AgentRunSource,
        preferVoice: Bool = false,
        createdAt: Date = Date()
    ) {
        self.id = id
        self.prompt = prompt
        self.source = source
        self.preferVoice = preferVoice
        self.createdAt = createdAt
    }
}

/// Permission domains voice input can request just-in-time.
enum AgentPermissionDomain: String, CaseIterable, Identifiable {
    case microphone
    case speech

    var id: String { rawValue }

    var title: String {
        switch self {
        case .microphone: return "Microphone"
        case .speech: return "Speech recognition"
        }
    }

    /// Short copy shown in-app immediately before the system dialog.
    var prePrompt: String {
        switch self {
        case .microphone:
            return "Device Agent needs the microphone for voice input."
        case .speech:
            return "Device Agent turns speech into text on-device before sending a prompt."
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

    var errorDescription: String? {
        switch self {
        case .permissionDenied(let domain):
            return "\(domain.title) access is denied. Enable it in Settings if you want voice input."
        case .permissionNeeded(let domain):
            return "\(domain.title) access is required."
        case .unavailable(let message):
            return message
        case .invalidArguments(let message):
            return message
        case .cancelled:
            return "Cancelled."
        }
    }
}
