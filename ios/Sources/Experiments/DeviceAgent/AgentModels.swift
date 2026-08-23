import Foundation

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
        case .observe: return "Read-only tools"
        case .act: return "Writes need confirmation"
        case .browse: return "In-app web demo"
        }
    }
}

/// One line in the on-screen transcript.
struct AgentTranscriptEntry: Identifiable, Equatable {
    enum Kind: Equatable {
        case user
        case assistant
        case toolCall(name: String, summary: String)
        case toolResult(name: String, summary: String)
        case system
        case permission(domain: String)
        case confirmation(summary: String)
    }

    let id: UUID
    let date: Date
    let kind: Kind
    let text: String

    init(id: UUID = UUID(), date: Date = Date(), kind: Kind, text: String) {
        self.id = id
        self.date = date
        self.kind = kind
        self.text = text
    }
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
