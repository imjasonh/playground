import Foundation

#if canImport(FoundationModels)
import FoundationModels
#endif

/// Runs prompts through on-device Foundation Models + in-app browser tools.
/// Unavailable without Apple Intelligence (iOS 26+ with the model ready).
@MainActor
final class AgentRuntime: ObservableObject {
    @Published var transcript: [AgentTranscriptEntry] = []
    @Published var isRunning = false
    @Published private(set) var modelGate: AgentModelGate = .unsupportedPlatform
    /// How full the on-device model context window is (0...1).
    @Published private(set) var contextUsage = AgentContextUsage.empty

    var isModelAvailable: Bool { modelGate.isAvailable }
    var modelStatusText: String { modelGate.detail }

    /// Latest user prompt — used to keep page findings relevant to the question.
    var lastUserPrompt: String = ""
    /// AFM page-extraction failures recorded for conversation export / iteration.
    private(set) var extractionDiagnostics: [AgentPageExtractionDiagnostic] = []

    let context: AgentToolContext

    private var budget = AgentContextBudget()
    private var lastPageFindings: [String] = []
    private var recentUserPrompts: [String] = []
    private var carryOverNotes: String = ""
    private var didCompactThisSession = false
    /// Holds `LanguageModelSession` when FoundationModels is linked (typed via helpers).
    private var languageSessionBox: Any?

    init(context: AgentToolContext? = nil) {
        self.context = context ?? AgentToolContext()
        refreshModelStatus()
        if isModelAvailable {
            appendSystem(AgentToolExecutor.helpText())
        }
        publishContextUsage()
    }

    func refreshModelStatus() {
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            modelGate = Self.gate(for: SystemLanguageModel.default.availability)
            refreshWindowSizeFromModel()
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

    @available(iOS 26.0, *)
    private func refreshWindowSizeFromModel() {
        // contextSize is available on newer SDKs (back-deployed). Fall back to 4096.
        let model = SystemLanguageModel.default
        if let size = Self.readContextSize(from: model), size > 0 {
            budget.windowTokens = size
            publishContextUsage()
        }
    }

    @available(iOS 26.0, *)
    private static func readContextSize(from model: SystemLanguageModel) -> Int? {
        // Avoid a hard dependency on iOS 26.4 SDK symbols in older toolchains.
        let mirror = Mirror(reflecting: model)
        for child in mirror.children {
            if child.label == "contextSize", let value = child.value as? Int {
                return value
            }
        }
        return nil
    }
    #endif

    func clearTranscript() {
        transcript.removeAll()
        extractionDiagnostics.removeAll()
        context.browser.clearReplay()
        lastPageFindings = []
        recentUserPrompts = []
        carryOverNotes = ""
        didCompactThisSession = false
        resetLanguageSession()
        if isModelAvailable {
            appendSystem(AgentToolExecutor.helpText())
        }
        publishContextUsage()
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
        recentUserPrompts.append(trimmed)
        if recentUserPrompts.count > 8 {
            recentUserPrompts.removeFirst(recentUserPrompts.count - 8)
        }
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
            if Self.isExceededContextWindow(error) {
                // Last-resort recovery: compact and retry once.
                compactLanguageSession(reason: "Model context filled; compacted and retrying.")
                do {
                    #if canImport(FoundationModels)
                    if #available(iOS 26.0, *) {
                        try await runFoundationModels(prompt: trimmed, isRetryAfterCompact: true)
                        return
                    }
                    #endif
                } catch {
                    append(.assistant, text: "Couldn’t finish after compacting context: \(error.localizedDescription)")
                    return
                }
            }
            append(.assistant, text: error.localizedDescription)
        }
    }

    #if canImport(FoundationModels)
    @available(iOS 26.0, *)
    private func runFoundationModels(prompt: String, isRetryAfterCompact: Bool = false) async throws {
        refreshModelStatus()
        guard isModelAvailable else {
            append(.system, text: modelStatusText)
            return
        }

        if !isRetryAfterCompact, budget.needsCompact {
            compactLanguageSession(reason: "Trimmed model context to leave room for this turn.")
        }

        let session = ensureLanguageSession()
        budget.addText(prompt)
        publishContextUsage()

        let response = try await session.respond(to: prompt)
        let text = response.content.trimmingCharacters(in: .whitespacesAndNewlines)
        budget.addText(text)
        publishContextUsage()
        append(.assistant, text: text.isEmpty ? "(Empty model response.)" : text)

        if budget.needsCompact {
            compactLanguageSession(reason: "Trimmed model context after that reply.")
        }
    }

    @available(iOS 26.0, *)
    private func ensureLanguageSession() -> LanguageModelSession {
        if let existing = languageSessionBox as? LanguageModelSession {
            return existing
        }
        let tools = makeFoundationTools()
        let session = LanguageModelSession(tools: tools, instructions: sessionInstructions)
        languageSessionBox = session
        budget.resetBaseline(instructions: sessionInstructions)
        publishContextUsage()
        return session
    }

    @available(iOS 26.0, *)
    private var sessionInstructions: String {
        var body = baseInstructions
        if !carryOverNotes.isEmpty {
            body += "\n\n" + carryOverNotes
        }
        return body
    }

    @available(iOS 26.0, *)
    private var baseInstructions: String {
        """
        You are Device Agent inside the Playground iOS app. Your only job is driving the in-app browser.
        Prefer cheap tools before another full browserSnapshot:
        - browserFind(query) to list matching controls (tiny)
        - browserClickText(text) to click by visible label without a ref
        - browserGet(ref) for one element's href/value/label
        - browserScroll(up|down|top|bottom|ref) to move the viewport
        - browserSelect(ref, option) for <select> controls
        Use browserOpen only if no useful page is open. Use browserSnapshot when you need extractedFindings or a fresh element map.
        browserSnapshot returns extractedFindings plus interactive element refs (page text omitted). Prefer extractedFindings for answers.
        Your final reply must be short bullet points from the page that answer the user question. Do not summarize the chat transcript.
        Keep the same browser tab for follow-ups unless they ask for a different site.
        Keep final answers short. Prefer one snapshot per turn when possible.
        """
    }

    @available(iOS 26.0, *)
    private func makeFoundationTools() -> [any Tool] {
        [
            GetDateTimeFMTool(runtime: self),
            BrowserOpenFMTool(runtime: self),
            BrowserReadFMTool(runtime: self),
            BrowserSnapshotFMTool(runtime: self),
            BrowserFindFMTool(runtime: self),
            BrowserClickFMTool(runtime: self),
            BrowserClickTextFMTool(runtime: self),
            BrowserTypeFMTool(runtime: self),
            BrowserSelectFMTool(runtime: self),
            BrowserGetFMTool(runtime: self),
            BrowserScrollFMTool(runtime: self),
            BrowserBackFMTool(runtime: self),
        ]
    }
    #else
    private func runFoundationModels(prompt: String, isRetryAfterCompact: Bool = false) async throws {
        _ = isRetryAfterCompact
        append(.system, text: modelStatusText)
    }
    #endif

    private func resetLanguageSession() {
        languageSessionBox = nil
        budget = AgentContextBudget(windowTokens: budget.windowTokens)
        publishContextUsage()
    }

    private func compactLanguageSession(reason: String) {
        carryOverNotes = AgentContextBudget.compactionCarryOver(
            url: context.browser.url?.absoluteString ?? context.browserURL?.absoluteString,
            title: context.browser.title.isEmpty ? context.browserTitle : context.browser.title,
            findings: lastPageFindings,
            recentUserPrompts: recentUserPrompts
        )
        didCompactThisSession = true
        resetLanguageSession()
        appendSystem(reason)
        publishContextUsage()
    }

    /// Snapshot scrape char budget for the current remaining context.
    var snapshotTextCharBudget: Int {
        budget.snapshotTextCharBudget()
    }

    func appendToolCall(name: String, arguments: String) {
        let detail = arguments.trimmingCharacters(in: .whitespacesAndNewlines)
        transcript.append(
            AgentTranscriptEntry(
                kind: .toolCall(name: name),
                text: "Invoking \(name)…",
                debugDetail: detail.isEmpty ? nil : detail
            )
        )
        budget.addText(name + detail)
        publishContextUsage()
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

    /// Logs the full tool result for export, runs page extraction for snapshots, and returns
    /// a **slim** payload for the LanguageModelSession so we stay under the context window.
    func appendToolResultAndEnrich(name: String, result: String) async throws -> String {
        appendToolResult(name: name, result: result)

        let maxChars = budget.modelToolResultCharBudget()
        guard name == "browserSnapshot" else {
            let slim = AgentContextBudget.truncateToChars(result, maxChars: maxChars)
            budget.addText(slim)
            publishContextUsage()
            return slim
        }

        let input = pageExtractionInput(fromSnapshotResult: result)
        let title = input.title
        let url = input.url
        let event = context.browser.replay.last(where: { $0.action == "snapshot" })
        let elements = event?.elements ?? []
        let headings = event?.headings ?? input.headings

        do {
            let bullets = try await AgentPageExtractor.extract(from: input)
            lastPageFindings = bullets
            let findings = AgentPageExtractor.formatFindings(title: title, url: url, bullets: bullets)
            transcript.append(
                AgentTranscriptEntry(
                    kind: .pageFindings,
                    text: findings,
                    debugDetail: bullets.joined(separator: "\n")
                )
            )
            let slim = AgentContextBudget.modelFacingSnapshot(
                title: title,
                url: url,
                elements: elements,
                headings: headings,
                extractedFindings: bullets,
                maxChars: budget.modelToolResultCharBudget()
            )
            budget.addText(slim)
            publishContextUsage()
            return slim
        } catch {
            let diagnostic = recordExtractionFailure(
                input: input,
                rawSnapshot: result,
                error: error
            )
            let failure = AgentPageExtractor.formatExtractionFailure(
                title: title,
                url: url,
                error: error
            )
            transcript.append(
                AgentTranscriptEntry(
                    kind: .pageFindings,
                    text: failure,
                    debugDetail: diagnosticDebugDetail(diagnostic)
                )
            )
            throw AgentToolError.unavailable(error.localizedDescription)
        }
    }

    private func pageExtractionInput(fromSnapshotResult result: String) -> AgentPageExtractor.Input {
        let event = context.browser.replay.last(where: { $0.action == "snapshot" })
        let title = event?.title ?? context.browser.title
        let url = event?.url ?? context.browser.url?.absoluteString ?? ""
        let pageText: String
        if let stored = event?.pageText, !stored.isEmpty {
            pageText = stored
        } else if let range = result.range(of: "text:\n") {
            pageText = String(result[range.upperBound...])
        } else {
            pageText = ""
        }
        return AgentPageExtractor.Input(
            userQuestion: lastUserPrompt,
            title: title,
            url: url,
            headings: event?.headings ?? [],
            listItems: event?.listItems ?? [],
            pageText: pageText
        )
    }

    @discardableResult
    private func recordExtractionFailure(
        input: AgentPageExtractor.Input,
        rawSnapshot: String,
        error: Error
    ) -> AgentPageExtractionDiagnostic {
        let unpacked = AgentPageExtractor.unpackError(error)
        let diagnostic = AgentPageExtractionDiagnostic(
            errorCode: unpacked.code,
            errorMessage: unpacked.message,
            userQuestion: input.userQuestion,
            title: input.title,
            url: input.url,
            headings: input.headings,
            listItems: input.listItems,
            pageText: String(input.pageText.prefix(8_000)),
            prompt: AgentPageExtractor.buildPrompt(from: input),
            modelGate: modelGate.title,
            modelAvailable: isModelAvailable,
            rawSnapshotPrefix: String(rawSnapshot.prefix(6_000)),
            rawModelBullets: unpacked.rawBullets
        )
        extractionDiagnostics.append(diagnostic)
        if extractionDiagnostics.count > 40 {
            extractionDiagnostics.removeFirst(extractionDiagnostics.count - 40)
        }
        return diagnostic
    }

    private func diagnosticDebugDetail(_ diagnostic: AgentPageExtractionDiagnostic) -> String {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.sortedKeys]
        encoder.dateEncodingStrategy = .iso8601
        if let data = try? encoder.encode(diagnostic),
           let text = String(data: data, encoding: .utf8) {
            return text
        }
        return diagnostic.errorMessage
    }

    func appendPermission(_ domain: AgentPermissionDomain) {
        transcript.append(
            AgentTranscriptEntry(
                kind: .permission(domain: domain.title),
                text: domain.prePrompt
            )
        )
    }

    private func publishContextUsage() {
        contextUsage = AgentContextUsage(budget: budget, didCompact: didCompactThisSession)
    }

    static func isExceededContextWindow(_ error: Error) -> Bool {
        let text = error.localizedDescription.lowercased()
        if text.contains("context window") || text.contains("exceededcontext") {
            return true
        }
        let ns = error as NSError
        if ns.domain.lowercased().contains("foundationmodels") {
            // GenerationError.exceededContextWindowSize has been observed as code -1.
            if ns.localizedDescription.lowercased().contains("context") {
                return true
            }
        }
        return false
    }

    /// JSON dump of the full transcript (including hidden tool results) for debugging.
    func makeConversationDump() -> AgentConversationDump {
        AgentConversationDump(
            exportedAt: Date(),
            mode: "browser",
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
            browserReplay: context.browser.replay,
            extractionDiagnostics: extractionDiagnostics
        )
    }

    func conversationDumpJSONLData() throws -> Data {
        try AgentConversationExporter.jsonlData(for: makeConversationDump())
    }

    func conversationDumpZipData() throws -> Data {
        try AgentConversationExporter.zipData(for: makeConversationDump())
    }

    /// Writes a `.jsonl.zip` suitable for sharing / attaching in chat.
    func writeConversationDumpFile() throws -> URL {
        let dump = makeConversationDump()
        let data = try AgentConversationExporter.zipData(for: dump)
        let name = AgentConversationExporter.filenameForZip(at: dump.exportedAt)
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
            return try await runtime.appendToolResultAndEnrich(name: name, result: result)
        }.value
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
    let description = "Read interactive element refs and extract question-relevant findings from the in-app browser. Call before click/type."

    @Generable
    struct Arguments {
        @Guide(description: "Max page-text characters to scrape (default comes from remaining context budget)")
        var maxTextChars: Double
    }

    func call(arguments: Arguments) async throws -> String {
        return try await AgentFMToolBridge.run(runtime, name: name, summary: "snapshot") { context in
            guard let runtime else {
                throw AgentToolError.unavailable("Device Agent runtime is gone.")
            }
            let requested = arguments.maxTextChars > 0 ? Int(arguments.maxTextChars) : runtime.snapshotTextCharBudget
            let capped = min(requested, runtime.snapshotTextCharBudget)
            return try await AgentToolExecutor.browserSnapshot(
                context: context,
                maxTextChars: Double(capped)
            )
        }
    }
}

@available(iOS 26.0, *)
struct BrowserClickFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserClick"
    let description = "Click an element by ref from the latest browserSnapshot or browserFind (for example \"3\")."

    @Generable
    struct Arguments {
        @Guide(description: "Numeric ref from browserSnapshot or browserFind")
        var ref: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.ref) { context in
            try await AgentToolExecutor.browserClick(context: context, ref: arguments.ref)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserClickTextFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserClickText"
    let description = "Click the first visible control whose label contains the given text. Prefer this over snapshot+click when the label is known."

    @Generable
    struct Arguments {
        @Guide(description: "Visible label substring to click (for example \"third result\" or \"Next\")")
        var text: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.text) { context in
            try await AgentToolExecutor.browserClickText(context: context, text: arguments.text)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserFindFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserFind"
    let description = "List interactive controls matching a query (label/href). Returns a short match list and refreshes refs. Cheaper than browserSnapshot."

    @Generable
    struct Arguments {
        @Guide(description: "Substring to match in control labels or hrefs (empty returns the first controls)")
        var query: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.query) { context in
            try await AgentToolExecutor.browserFind(context: context, query: arguments.query)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserGetFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserGet"
    let description = "Read one element by ref: kind, label, href, value. Tiny result."

    @Generable
    struct Arguments {
        @Guide(description: "Numeric ref from browserSnapshot or browserFind")
        var ref: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.ref) { context in
            try await AgentToolExecutor.browserGet(context: context, ref: arguments.ref)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserScrollFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserScroll"
    let description = "Scroll the page: up, down, top, bottom, or a ref to bring that element into view."

    @Generable
    struct Arguments {
        @Guide(description: "up | down | top | bottom | numeric ref")
        var directionOrRef: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.directionOrRef) { context in
            try await AgentToolExecutor.browserScroll(context: context, directionOrRef: arguments.directionOrRef)
        }
    }
}

@available(iOS 26.0, *)
struct BrowserSelectFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserSelect"
    let description = "Choose an option on a <select> by visible label or value."

    @Generable
    struct Arguments {
        @Guide(description: "Numeric ref of the select from browserSnapshot or browserFind")
        var ref: String
        @Guide(description: "Option label or value to select")
        var option: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await AgentFMToolBridge.run(runtime, name: name, summary: arguments.ref) { context in
            try await AgentToolExecutor.browserSelect(
                context: context,
                ref: arguments.ref,
                option: arguments.option
            )
        }
    }
}

@available(iOS 26.0, *)
struct BrowserTypeFMTool: Tool {
    weak var runtime: AgentRuntime?
    let name = "browserType"
    let description = "Type into an input/textarea by ref from browserSnapshot or browserFind. Set submit true to press Enter / submit the form."

    @Generable
    struct Arguments {
        @Guide(description: "Numeric ref from browserSnapshot or browserFind")
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
