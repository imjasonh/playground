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

    /// Latest user prompt — used to keep page findings relevant to the question.
    var lastUserPrompt: String = ""

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
        context.browser.clearReplay()
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

        lastUserPrompt = trimmed
        append(.user, text: trimmed, sourceNote: source)

        do {
            #if canImport(FoundationModels)
            if #available(iOS 26.0, *) {
                try await runFoundationModels(prompt: trimmed)
            } else {
                append(.system, text: modelStatusText)
            }
            #else
            try await runFoundationModels(prompt: trimmed)
            #endif
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
        Use the in-app browser for web questions: browserOpen (only if no useful page is open) → browserSnapshot → optional browserClick / browserType → browserSnapshot again.
        browserSnapshot returns raw scrape plus extractedFindings (Foundation Model bullets from the page). Prefer those bullets for your answer; dig with click/type only if needed.
        Your final reply must be short bullet points from the page that answer the user question. Do not summarize the chat transcript.
        Keep the same browser tab for follow-ups unless they ask for a different site.
        Use openURL only when the user wants Safari or another system handler.
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
            BrowserOpenFMTool(runtime: self),
            BrowserReadFMTool(runtime: self),
            BrowserSnapshotFMTool(runtime: self),
            BrowserClickFMTool(runtime: self),
            BrowserTypeFMTool(runtime: self),
            BrowserBackFMTool(runtime: self),
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

    func appendToolCall(name: String, arguments: String) {
        let detail = arguments.trimmingCharacters(in: .whitespacesAndNewlines)
        transcript.append(
            AgentTranscriptEntry(
                kind: .toolCall(name: name),
                text: "Invoking \(name)…",
                debugDetail: detail.isEmpty ? nil : detail
            )
        )
    }

    func appendToolResult(name: String, result: String) {
        transcript.append(
            AgentTranscriptEntry(
                kind: .toolResult(name: name),
                text: "",
                debugDetail: result
            )
        )
    }

    /// Logs the tool result, runs Foundation Model extraction for snapshots, and returns
    /// an enriched payload the agent session can use (raw scrape + extractedFindings).
    func appendToolResultAndEnrich(name: String, result: String) async -> String {
        appendToolResult(name: name, result: result)
        guard name == "browserSnapshot" else { return result }
        let bullets = await extractPageFindingsBullets(fromSnapshotResult: result)
        let event = context.browser.replay.last(where: { $0.action == "snapshot" })
        let title = event?.title ?? context.browser.title ?? ""
        let url = event?.url ?? context.browser.url?.absoluteString ?? ""
        let findings = AgentPageExtractor.formatFindings(title: title, url: url, bullets: bullets)
        transcript.append(
            AgentTranscriptEntry(
                kind: .pageFindings,
                text: findings,
                debugDetail: bullets.joined(separator: "\n")
            )
        )
        guard !bullets.isEmpty else { return result }
        let extracted = bullets.map { "• \($0)" }.joined(separator: "\n")
        return """
        \(result)

        extractedFindings (relevant to user question):
        \(extracted)
        """
    }

    private func extractPageFindingsBullets(fromSnapshotResult result: String) async -> [String] {
        let event = context.browser.replay.last(where: { $0.action == "snapshot" })
        let title = event?.title ?? context.browser.title ?? ""
        let url = event?.url ?? context.browser.url?.absoluteString ?? ""
        let pageText: String
        if let stored = event?.pageText, !stored.isEmpty {
            pageText = stored
        } else if let range = result.range(of: "text:\n") {
            pageText = String(result[range.upperBound...])
        } else {
            pageText = ""
        }
        return await AgentPageExtractor.extract(
            from: AgentPageExtractor.Input(
                userQuestion: lastUserPrompt,
                title: title,
                url: url,
                headings: event?.headings ?? [],
                listItems: event?.listItems ?? [],
                pageText: pageText
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

    /// JSON dump of the full transcript (including hidden tool results) for debugging.
    func makeConversationDump() -> AgentConversationDump {
        AgentConversationDump(
            exportedAt: Date(),
            mode: context.mode.rawValue,
            modelGate: modelGate.title,
            modelAvailable: isModelAvailable,
            entries: transcript.map { entry in
                AgentConversationDumpEntry(
                    id: entry.id.uuidString,
                    date: entry.date,
                    kind: entry.kindLabel,
                    toolName: entry.toolName,
                    displayText: entry.text,
                    debugDetail: entry.debugDetail
                )
            },
            toolLog: context.lastToolLog.map {
                AgentConversationDumpToolLog(name: $0.name, detail: $0.detail)
            },
            browserReplay: context.browser.replay
        )
    }

    func conversationDumpJSONData() throws -> Data {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        encoder.dateEncodingStrategy = .iso8601
        return try encoder.encode(makeConversationDump())
    }

    func writeConversationDumpFile() throws -> URL {
        let data = try conversationDumpJSONData()
        let name = "device-agent-\(ISO8601DateFormatter().string(from: Date()).replacingOccurrences(of: ":", with: "-")).json"
        let url = FileManager.default.temporaryDirectory.appendingPathComponent(name)
        try data.write(to: url, options: .atomic)
        return url
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
        work: @escaping @MainActor (AgentToolContext) async throws -> String
    ) async throws -> String {
        try await Task { @MainActor in
            guard let runtime else {
                throw AgentToolError.unavailable("Device Agent runtime is gone.")
            }
            runtime.appendToolCall(name: name, arguments: summary)
            if let permission {
                runtime.appendPermission(permission)
            }
            let result = try await work(runtime.context)
            return await runtime.appendToolResultAndEnrich(name: name, result: result)
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
struct BrowserOpenFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserOpen"
    let description = "Load a real http(s) URL in the in-app web view (not Safari). Then call browserSnapshot."

    @Generable
    struct Arguments {
        @Guide(description: "Absolute http or https URL")
        var url: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.url) { context in
            try await AgentToolExecutor.browserOpen(context: context, urlString: arguments.url)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserReadFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserRead"
    let description = "Read the current in-app browser title, URL, and loading state."

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

@available(iOS 26.0, *)
struct BrowserSnapshotFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserSnapshot"
    let description = "Read interactive elements (with numeric refs) and visible text from the in-app browser. Call before click/type."

    @Generable
    struct Arguments {
        @Guide(description: "Max visible text characters to return (default 3500)")
        var maxTextChars: Double
    }

    func call(arguments: Arguments) async throws -> String {
        let maxChars = arguments.maxTextChars > 0 ? arguments.maxTextChars : 3500
        return try await AgentFMToolBridge.run(runtime, name: name, summary: "max=\(Int(maxChars))") { context in
            try await AgentToolExecutor.browserSnapshot(context: context, maxTextChars: maxChars)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserClickFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserClick"
    let description = "Click an element by ref from the latest browserSnapshot (for example \"3\")."

    @Generable
    struct Arguments {
        @Guide(description: "Numeric ref from browserSnapshot")
        var ref: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.ref) { context in
            try await AgentToolExecutor.browserClick(context: context, ref: arguments.ref)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserTypeFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserType"
    let description = "Type into an input/textarea by ref from browserSnapshot. Set submit true to press Enter / submit the form."

    @Generable
    struct Arguments {
        @Guide(description: "Numeric ref from browserSnapshot")
        var ref: String
        @Guide(description: "Text to enter")
        var text: String
        @Guide(description: "If true, submit the form or press Enter after typing")
        var submit: Bool
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.ref) { context in
            try await AgentToolExecutor.browserType(
                context: context,
                ref: arguments.ref,
                text: arguments.text,
                submit: arguments.submit
            )
        }
    }
}

@available(iOS 26.0, *)
struct BrowserBackFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserBack"
    let description = "Go back in the in-app browser history."

    @Generable
    struct Arguments {
        @Guide(description: "Unused; pass an empty string")
        var note: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name) { context in
            try await AgentToolExecutor.browserBack(context: context)
        }
    }
}
#endif
