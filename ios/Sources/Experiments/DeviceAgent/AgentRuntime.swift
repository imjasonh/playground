import Foundation

#if canImport(FoundationModels)
import FoundationModels
#endif

/// Runs prompts through on-device Foundation Models + tools. Unavailable without
/// Apple Intelligence (iOS 26+ with the model ready).
@MainActor
final class AgentRuntime: ObservableObject {
    @Published var transcript: [AgentTranscriptEntry] = []
    @Published var isRunning = false
    @Published private(set) var modelGate: AgentModelGate = .unsupportedPlatform

    var isModelAvailable: Bool { modelGate.isAvailable }
    var modelStatusText: String { modelGate.detail }

    let context: AgentToolContext

    init(context: AgentToolContext? = nil) {
        self.context = context ?? AgentToolContext()
        refreshModelStatus()
        if isModelAvailable {
            appendSystem(AgentToolExecutor.helpText(mode: self.context.mode))
        }
    }

    func refreshModelStatus() {
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            modelGate = Self.gate(for: SystemLanguageModel.default.availability)
            return
        }
        #endif
        modelGate = .unsupportedPlatform
    }

    /// Primary CTA for the unavailable pane (Settings or check-again).
    func performModelGateAction(_ action: AgentModelGateAction) async {
        switch action {
        case .openAppleIntelligenceSettings:
            await AgentAppleIntelligenceSettings.open()
        case .checkAgain:
            refreshModelStatus()
            if isModelAvailable {
                clearTranscript()
            }
        }
    }

    #if canImport(FoundationModels)
    @available(iOS 26.0, *)
    private static func gate(for availability: SystemLanguageModel.Availability) -> AgentModelGate {
        switch availability {
        case .available:
            return .available
        case .unavailable(.deviceNotEligible):
            return .deviceNotEligible
        case .unavailable(.appleIntelligenceNotEnabled):
            return .needsAppleIntelligence
        case .unavailable(.modelNotReady):
            return .modelNotReady
        case .unavailable(let reason):
            return .other("Apple Intelligence isn’t available (\(String(describing: reason))).")
        @unknown default:
            return .other("Apple Intelligence isn’t available on this device.")
        }
    }
    #endif

    func clearTranscript() {
        transcript.removeAll()
        if isModelAvailable {
            appendSystem(AgentToolExecutor.helpText(mode: context.mode))
        }
    }

    func send(prompt: String, source: AgentRunSource) async {
        let trimmed = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return }
        guard !isRunning else { return }

        refreshModelStatus()
        guard isModelAvailable else {
            append(.system, text: modelStatusText)
            return
        }

        isRunning = true
        defer { isRunning = false }

        append(.user, text: trimmed, sourceNote: source)

        do {
            try await runFoundationModels(prompt: trimmed)
        } catch {
            append(.assistant, text: error.localizedDescription)
        }
    }

    #if canImport(FoundationModels)
    @available(iOS 26.0, *)
    private func runFoundationModels(prompt: String) async throws {
        refreshModelStatus()
        guard isModelAvailable else {
            append(.system, text: modelStatusText)
            return
        }

        let tools = makeFoundationTools()
        let session = LanguageModelSession(tools: tools, instructions: instructions)
        append(.system, text: "Foundation Model session started with \(tools.count) tools.")
        let response = try await session.respond(to: prompt)
        let text = response.content.trimmingCharacters(in: .whitespacesAndNewlines)
        append(.assistant, text: text.isEmpty ? "(Empty model response.)" : text)
    }

    @available(iOS 26.0, *)
    private var instructions: String {
        """
        You are Device Agent inside the Playground iOS app.
        Use tools to act on the phone. Request only what you need.
        For calendar, SMS, and email drafts, tools will ask the user to confirm.
        Prefer listAttachments / readTextAttachment for files the user shared.
        Use browserLoadDemo for the bundled Demo Mail page — do not invent Gmail automation.
        Keep final answers short. Mode is \(context.mode.title).
        """
    }

    @available(iOS 26.0, *)
    private func makeFoundationTools() -> [any Tool] {
        var tools: [any Tool] = [
            ListAttachmentsFMTool(runtime: self),
            ReadTextAttachmentFMTool(runtime: self),
            GetDateTimeFMTool(runtime: self),
            OpenURLFMTool(runtime: self),
            SearchContactsFMTool(runtime: self),
            GetLocationFMTool(runtime: self),
            OpenMapsFMTool(runtime: self),
            BrowserLoadDemoFMTool(runtime: self),
            BrowserReadFMTool(runtime: self),
        ]
        if context.mode == .act {
            tools.append(CreateEventFMTool(runtime: self))
            tools.append(DraftSMSFMTool(runtime: self))
            tools.append(DraftEmailFMTool(runtime: self))
        }
        return tools
    }
    #else
    private func runFoundationModels(prompt: String) async throws {
        append(.system, text: modelStatusText)
    }
    #endif

    func appendToolCall(name: String, summary: String) {
        transcript.append(
            AgentTranscriptEntry(
                kind: .toolCall(name: name, summary: summary),
                text: "→ \(name) \(summary)".trimmingCharacters(in: .whitespaces)
            )
        )
    }

    func appendToolResult(name: String, summary: String) {
        transcript.append(
            AgentTranscriptEntry(
                kind: .toolResult(name: name, summary: summary),
                text: "← \(name): \(summary)"
            )
        )
    }

    func appendPermission(_ domain: AgentPermissionDomain) {
        transcript.append(
            AgentTranscriptEntry(
                kind: .permission(domain: domain.title),
                text: domain.prePrompt
            )
        )
    }

    private func appendSystem(_ text: String) {
        append(.system, text: text)
    }

    private func append(_ kind: AgentTranscriptEntry.Kind, text: String, sourceNote: AgentRunSource? = nil) {
        var body = text
        if let sourceNote, sourceNote != .chat {
            body = "[\(sourceNote.rawValue)] \(text)"
        }
        transcript.append(AgentTranscriptEntry(kind: kind, text: body))
    }
}

#if canImport(FoundationModels)
@available(iOS 26.0, *)
private enum AgentFMToolBridge {
    static func run(
        _ runtime: AgentRuntime?,
        name: String,
        summary: String = "",
        permission: AgentPermissionDomain? = nil,
        work: @MainActor (AgentToolContext) async throws -> String
    ) async throws -> String {
        try await Task { @MainActor in
            guard let runtime else {
                throw AgentToolError.unavailable("Device Agent runtime is gone.")
            }
            runtime.appendToolCall(name: name, summary: summary)
            if let permission {
                runtime.appendPermission(permission)
            }
            let result = try await work(runtime.context)
            runtime.appendToolResult(name: name, summary: String(result.prefix(200)))
            return result
        }.value
    }
}

@available(iOS 26.0, *)
struct ListAttachmentsFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "listAttachments"
    let description = "List files in the Device Agent inbox (from Shortcuts or in-app attach)."

    @Generable
    struct Arguments {
        @Guide(description: "Unused; pass an empty string")
        var note: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name) { context in
            AgentToolExecutor.listAttachments(context: context)
        }
    }
}

@available(iOS 26.0, *)
struct ReadTextAttachmentFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "readTextAttachment"
    let description = "Read a text attachment by filename substring or id prefix."

    @Generable
    struct Arguments {
        @Guide(description: "Filename or id fragment")
        var filenameQuery: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.filenameQuery) { context in
            try AgentToolExecutor.readTextAttachment(
                context: context,
                filenameQuery: arguments.filenameQuery
            )
        }
    }
}

@available(iOS 26.0, *)
struct GetDateTimeFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "getCurrentDateTime"
    let description = "Return the current local date and time."

    @Generable
    struct Arguments {
        @Guide(description: "Unused; pass an empty string")
        var note: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name) { _ in
            AgentToolExecutor.getCurrentDateTime()
        }
    }
}

@available(iOS 26.0, *)
struct OpenURLFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "openURL"
    let description = "Open an absolute http(s) or other URL in the system browser or handler."

    @Generable
    struct Arguments {
        var url: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.url) { _ in
            try AgentToolExecutor.openURL(arguments.url)
        }
    }
}

@available(iOS 26.0, *)
struct SearchContactsFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "searchContacts"
    let description = "Search device Contacts by name. Requests Contacts permission just-in-time."

    @Generable
    struct Arguments {
        var query: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(
            runtime,
            name: name,
            summary: arguments.query,
            permission: .contacts
        ) { context in
            try await AgentToolExecutor.searchContacts(context: context, query: arguments.query)
        }
    }
}

@available(iOS 26.0, *)
struct GetLocationFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "getCurrentLocation"
    let description = "Get the current GPS location. Requests Location permission just-in-time."

    @Generable
    struct Arguments {
        @Guide(description: "Unused; pass an empty string")
        var note: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(
            runtime,
            name: name,
            permission: .location
        ) { context in
            try await AgentToolExecutor.getCurrentLocation(context: context)
        }
    }
}

@available(iOS 26.0, *)
struct OpenMapsFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "openMapsDirections"
    let description = "Open Apple Maps with driving directions to a destination query."

    @Generable
    struct Arguments {
        var query: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.query) { _ in
            try AgentToolExecutor.openMapsDirections(query: arguments.query)
        }
    }
}

@available(iOS 26.0, *)
struct CreateEventFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "createCalendarEvent"
    let description = "Create a calendar event after user confirmation. hoursFromNow defaults to 2."

    @Generable
    struct Arguments {
        var title: String
        var notes: String
        var hoursFromNow: Double
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(
            runtime,
            name: name,
            summary: arguments.title,
            permission: .calendars
        ) { context in
            try await AgentToolExecutor.createCalendarEvent(
                context: context,
                title: arguments.title,
                notes: arguments.notes,
                hoursFromNow: arguments.hoursFromNow
            )
        }
    }
}

@available(iOS 26.0, *)
struct DraftSMSFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "draftSMS"
    let description = "Open an SMS/iMessage draft after confirmation. recipients is a comma-separated phone list."

    @Generable
    struct Arguments {
        var recipients: String
        var body: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.recipients) { context in
            try await AgentToolExecutor.draftSMS(
                context: context,
                recipients: arguments.recipients,
                body: arguments.body
            )
        }
    }
}

@available(iOS 26.0, *)
struct DraftEmailFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "draftEmail"
    let description = "Open a Mail draft after confirmation."

    @Generable
    struct Arguments {
        var to: String
        var subject: String
        var body: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.to) { context in
            try await AgentToolExecutor.draftEmail(
                context: context,
                to: arguments.to,
                subject: arguments.subject,
                body: arguments.body
            )
        }
    }
}

@available(iOS 26.0, *)
struct BrowserLoadDemoFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserLoadDemo"
    let description = "Load the bundled Demo Mail HTML page into the in-app web view."

    @Generable
    struct Arguments {
        @Guide(description: "Unused; pass an empty string")
        var note: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name) { context in
            AgentToolExecutor.browserLoadDemo(context: context)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserReadFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserRead"
    let description = "Read the current in-app browser title and URL."

    @Generable
    struct Arguments {
        @Guide(description: "Unused; pass an empty string")
        var note: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name) { context in
            AgentToolExecutor.browserRead(context: context)
        }
    }
}
#endif
