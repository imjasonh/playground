import Combine
import Foundation
import FoundationModels

/// Chat transcript row for Army List on-device assistance.
struct ArmyListChatEntry: Identifiable, Equatable {
    enum Kind: Equatable {
        case user
        case assistant
        case system
        case tool
    }

    let id: UUID
    let kind: Kind
    let text: String
    let createdAt: Date

    init(id: UUID = UUID(), kind: Kind, text: String, createdAt: Date = Date()) {
        self.id = id
        self.kind = kind
        self.text = text
        self.createdAt = createdAt
    }
}

/// Runs Army List prompts through on-device Foundation Models + list tools.
@MainActor
final class ArmyListChatRuntime: ObservableObject {
    /// How the session is configured. Chat keeps language tools only; builder
    /// is unused by construction (Laya / greedy owns the roster).
    enum Mode {
        case chat
        case builder
    }

    /// Roster actions the Laya controller owns. Theme / Weaknesses stay on
    /// Foundation Models.
    enum ConstructionAction {
        case build
        case fill
        case fix

        var title: String {
            switch self {
            case .build: return "Build list"
            case .fill: return "Fill points"
            case .fix: return "Fix errors"
            }
        }
    }

    /// Rough cost of the army-list tool schemas registered with the session.
    /// Matches `OnDeviceContextManager.safetyBufferTokens` (TN3193 tool + reply headroom).
    static let toolsReserveTokens = OnDeviceContextManager.safetyBufferTokens

    @Published var transcript: [ArmyListChatEntry] = []
    @Published var isRunning = false
    @Published private(set) var modelGate: AgentModelGate = .other("Checking Apple Intelligence availability.")
    @Published private(set) var contextUsage = AgentContextUsage.empty
    @Published private(set) var lastConstructionStep: ArmyListDecisionStep?

    let workspace: ArmyListChatWorkspace
    let mode: Mode

    /// Builder-mode starter builds use this to advance the New list progress UI
    /// when `applyRosterPlan` starts running.
    var onStarterBuildToolStarted: (@MainActor (String) -> Void)?

    private var languageSession: LanguageModelSession?
    private var workspaceBag: AnyCancellable?
    private var carryOverNotes = ""
    private var budget = AgentContextBudget(toolsReserveTokens: ArmyListChatRuntime.toolsReserveTokens)
    private var didCompactThisSession = false
    /// Full tool payloads for export (may be longer than what the model received).
    private(set) var toolLog: [(name: String, detail: String)] = []

    var isModelAvailable: Bool { modelGate.isAvailable }

    init(workspace: ArmyListChatWorkspace, mode: Mode = .chat) {
        self.workspace = workspace
        self.mode = mode
        workspaceBag = workspace.objectWillChange.sink { [weak self] _ in
            self?.objectWillChange.send()
        }
        refreshModelStatus()
        if mode == .chat {
            append(.system, text: Self.welcomeText)
        }
        publishContextUsage()
    }

    func refreshModelStatus() {
        modelGate = Self.gate(for: SystemLanguageModel.default.availability)
        if isModelAvailable {
            let size = SystemLanguageModel.default.contextSize
            if size > 0 {
                budget.windowTokens = size
                publishContextUsage()
            }
        }
    }

    func performModelGateAction(_ action: AgentModelGateAction) async {
        switch action {
        case .openAppleIntelligenceSettings:
            await AgentAppleIntelligenceSettings.open()
        case .checkAgain:
            refreshModelStatus()
            if isModelAvailable {
                transcript.removeAll()
                toolLog.removeAll()
                resetLanguageSession()
                append(.system, text: Self.welcomeText)
            }
        }
    }

    func clearTranscript() {
        transcript.removeAll()
        toolLog.removeAll()
        resetLanguageSession()
        lastConstructionStep = nil
        append(
            .system,
            text: "Transcript cleared. The list itself is unchanged."
        )
    }

    func send(prompt: String, displayText: String? = nil) async {
        let trimmed = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return }
        let shown = (displayText ?? trimmed).trimmingCharacters(in: .whitespacesAndNewlines)
        append(.user, text: shown.isEmpty ? trimmed : shown)
        isRunning = true
        defer { isRunning = false }

        do {
            try await runFoundationModels(prompt: trimmed)
        } catch {
            if OnDeviceContextManager.isExceededContextWindow(error) {
                compactLanguageSession(
                    reason: "Model context filled during tool use; compacted and retrying once."
                )
                do {
                    try await runFoundationModels(prompt: trimmed, isRetryAfterCompact: true)
                    return
                } catch {
                    append(
                        .assistant,
                        text: "Couldn’t finish after compacting context: \(error.localizedDescription). Try Clear, then ask for a smaller change."
                    )
                    return
                }
            }
            append(.assistant, text: friendlyGenerationError(error))
        }
    }

    /// Recognizes the typed iOS 27 context error and wrapped errors that retain
    /// a context-size description.
    nonisolated static func isExceededContextWindow(_ error: Error) -> Bool {
        OnDeviceContextManager.isExceededContextWindow(error)
    }

    private func friendlyGenerationError(_ error: Error) -> String {
        if OnDeviceContextManager.isExceededContextWindow(error) {
            return "The on-device model ran out of context. Tap Clear, then ask Theme or Weaknesses again."
        }
        return error.localizedDescription
    }

    private func resetLanguageSession() {
        languageSession = nil
        budget = AgentContextBudget(
            windowTokens: budget.windowTokens,
            toolsReserveTokens: Self.toolsReserveTokens
        )
        didCompactThisSession = false
        carryOverNotes = ""
        publishContextUsage()
    }

    private func compactLanguageSession(reason: String) {
        carryOverNotes = Self.compactionCarryOver(
            listSnapshot: workspace.compactSummary(maxIssues: 4),
            transcript: transcript
        )
        didCompactThisSession = true
        if let languageSession,
           let rehydrated = OnDeviceContextManager.rehydratedSession(
               from: languageSession,
               tools: makeFoundationTools()
           )
        {
            self.languageSession = rehydrated
            budget = AgentContextBudget(
                windowTokens: budget.windowTokens,
                toolsReserveTokens: Self.toolsReserveTokens
            )
            budget.resetBaseline(
                instructions: sessionInstructions,
                toolsReserveTokens: Self.toolsReserveTokens
            )
            budget.addText(carryOverNotes)
        } else {
            languageSession = nil
            budget = AgentContextBudget(
                windowTokens: budget.windowTokens,
                toolsReserveTokens: Self.toolsReserveTokens
            )
        }
        append(.system, text: reason)
        publishContextUsage()
    }

    /// Fresh-session notes after compact so follow-ups keep list + recent turns.
    /// Older turns compress into a rolling archive (TN3193 sliding-window pattern).
    nonisolated static func compactionCarryOver(
        listSnapshot: String,
        transcript: [ArmyListChatEntry]
    ) -> String {
        var parts: [String] = [
            "Prior model context was compacted.",
            "Answer ONLY the latest user message. Do not continue an earlier topic unless that message asks for it.",
        ]
        let snap = listSnapshot.trimmingCharacters(in: .whitespacesAndNewlines)
        if !snap.isEmpty {
            parts.append("List snapshot:")
            parts.append(String(snap.prefix(800)))
        }
        let turns: [OnDeviceContextManager.Turn] = transcript.compactMap { entry in
            switch entry.kind {
            case .user:
                return OnDeviceContextManager.Turn(role: .user, content: entry.text)
            case .assistant:
                return OnDeviceContextManager.Turn(role: .assistant, content: entry.text)
            case .system, .tool:
                return nil
            }
        }
        let summary = OnDeviceContextManager.rollingSummary(turns: turns)
        if !summary.isEmpty {
            parts.append(summary)
        }
        return AgentContextBudget.truncateToChars(
            parts.joined(separator: "\n"),
            maxChars: OnDeviceContextManager.carryOverMaxChars
        )
    }

    func noteToolExchange(name: String, result: String) -> String {
        toolLog.append((name: name, detail: result))
        let capped = AgentContextBudget.truncateToChars(
            result,
            maxChars: budget.modelToolResultCharBudget(default: 1_600)
        )
        budget.addText(name)
        budget.addText(capped)
        publishContextUsage()
        return capped
    }

    func makeConversationDump() -> ArmyListChatDump {
        let validation = workspace.validation
        return ArmyListChatDump(
            exportedAt: Date(),
            mode: "army-list-chat",
            modelGate: modelGate.title,
            modelAvailable: isModelAvailable,
            contextPercentUsed: contextUsage.percentUsed,
            contextDidCompact: contextUsage.didCompact,
            catalogVersion: workspace.catalog.version,
            list: workspace.list,
            validation: ArmyListChatDumpValidation(
                isLegal: validation.isLegal,
                totalPoints: validation.totalPoints,
                detachmentPointsSpent: validation.detachmentPointsSpent,
                errors: validation.errors.map {
                    ArmyListChatDumpIssue(
                        code: $0.code,
                        severity: $0.severity.rawValue,
                        message: $0.message,
                        unitID: $0.unitID?.uuidString
                    )
                },
                warnings: validation.warnings.map {
                    ArmyListChatDumpIssue(
                        code: $0.code,
                        severity: $0.severity.rawValue,
                        message: $0.message,
                        unitID: $0.unitID?.uuidString
                    )
                }
            ),
            entries: transcript.map { entry in
                let kindLabel: String
                switch entry.kind {
                case .user: kindLabel = "user"
                case .assistant: kindLabel = "assistant"
                case .system: kindLabel = "system"
                case .tool: kindLabel = "tool"
                }
                return ArmyListChatDumpEntry(
                    id: entry.id.uuidString,
                    date: entry.createdAt,
                    kind: kindLabel,
                    text: entry.text
                )
            },
            toolLog: toolLog.map {
                ArmyListChatDumpToolLog(name: $0.name, detail: $0.detail)
            }
        )
    }

    func writeConversationDumpFile() throws -> URL {
        try ArmyListChatDumpExporter.writeFile(for: makeConversationDump())
    }

    private func publishContextUsage() {
        contextUsage = AgentContextUsage(budget: budget, didCompact: didCompactThisSession)
    }

    private func append(_ kind: ArmyListChatEntry.Kind, text: String) {
        transcript.append(ArmyListChatEntry(kind: kind, text: text))
    }

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

    private func runFoundationModels(prompt: String, isRetryAfterCompact: Bool = false) async throws {
        refreshModelStatus()
        guard isModelAvailable else {
            append(.system, text: armyListGateDetail)
            return
        }
        if !isRetryAfterCompact, budget.needsCompact {
            compactLanguageSession(reason: "Trimmed model context to leave room for this turn.")
        }
        if isRetryAfterCompact, carryOverNotes.isEmpty {
            carryOverNotes = Self.compactionCarryOver(
                listSnapshot: workspace.compactSummary(maxIssues: 4),
                transcript: transcript
            )
        }
        let session = ensureLanguageSession()
        // Rehydrated sessions already have instructions from transcript.first;
        // inject list/chat carry-over on the prompt instead.
        let promptForModel: String
        if !carryOverNotes.isEmpty {
            promptForModel = OnDeviceContextManager.promptWithCarryOver(
                prompt: prompt,
                carryOver: carryOverNotes
            )
            carryOverNotes = ""
        } else {
            promptForModel = prompt
        }
        budget.addText(promptForModel)
        publishContextUsage()
        let response = try await session.respond(to: promptForModel)
        let text = response.content.trimmingCharacters(in: .whitespacesAndNewlines)
        budget.reconcileMeasuredUsage(totalTokens: response.usage.totalTokenCount)
        publishContextUsage()
        append(.assistant, text: text.isEmpty ? "(Empty model response.)" : text)
        if budget.needsCompact {
            compactLanguageSession(reason: "Trimmed model context after that reply.")
        }
    }

    private func ensureLanguageSession() -> LanguageModelSession {
        if let languageSession {
            return languageSession
        }
        var instructions = sessionInstructions
        if !carryOverNotes.isEmpty {
            instructions += "\n\n" + carryOverNotes
            carryOverNotes = ""
        }
        let session = LanguageModelSession(tools: makeFoundationTools(), instructions: instructions)
        languageSession = session
        budget.resetBaseline(
            instructions: instructions,
            toolsReserveTokens: Self.toolsReserveTokens
        )
        publishContextUsage()
        return session
    }

    private var sessionInstructions: String {
        if mode == .builder {
            return builderInstructions
        }
        return chatInstructions
    }

    /// Left in place for the unused builder session mode. Construction no longer
    /// goes through Foundation Models.
    private var builderInstructions: String {
        """
        You discuss a Warhammer 40,000 army list. Do not call tools that change the roster.
        """
    }

    private var chatInstructions: String {
        """
        You help the user name and discuss a Warhammer 40,000 11th Edition army list inside the Playground app.
        Faction for this list is fixed to whatever getListSummary reports. Do not switch factions.
        Construction (build, fill, fix) is done by the Laya controller, not by you. Do not invent datasheet ids or points.
        Call getListSummary when you need the current roster, points, or issues.
        For Theme, suggest a name and a paint color scheme. If the user wants that name, call setListName.
        For Weaknesses, give matchup opinions and label them as opinions.
        Prefer short replies. Format with Markdown: put a blank line between paragraphs and between matchup/section blocks, use **bold** for headings, and put each Weakness / Countermeasure on its own line. Never run sections together on one line.
        Always answer the latest user message; do not keep talking about an earlier Theme/name request unless they ask again.
        """
    }

    private func makeFoundationTools() -> [any Tool] {
        if mode == .builder {
            return []
        }
        return [
            ArmyGetListSummaryFMTool(runtime: self),
            ArmySetListNameFMTool(runtime: self),
        ]
    }

    /// Tool names registered with the current session. Tests use this.
    var foundationToolNames: [String] {
        makeFoundationTools().map(\.name)
    }

    /// Runs Build / Fill / Fix through the Laya controller. Prepares the
    /// shared graph when a download is already on disk.
    func runConstruction(
        _ action: ConstructionAction,
        theme: String,
        store: LayaModelStore? = nil
    ) async {
        guard !isRunning else { return }
        let store = store ?? LayaModelStore.shared
        beginConstruction(title: action.title)
        lastConstructionStep = nil
        defer {
            if isRunning { isRunning = false }
        }
        if store.isDownloaded, !store.isReady {
            await store.prepare()
        }
        if Task.isCancelled {
            failConstruction("Cancelled.")
            return
        }
        let decider = ArmyListDecisionController.activeDecider(store: store)
        let usedLaya = ArmyListDecisionController.usedLaya(store: store)
        let onStep: @MainActor (ArmyListDecisionStep) -> Void = { [weak self] step in
            self?.noteConstructionStep(step)
        }
        let result: ArmyListConstructionResult?
        switch action {
        case .build:
            result = await ArmyListDecisionController.build(
                catalog: workspace.catalog,
                factionID: workspace.list.factionID,
                battleSizeID: workspace.list.battleSizeID,
                theme: theme,
                userName: keptListName(),
                decider: decider,
                usedLaya: usedLaya,
                onStep: onStep
            )
            if let result {
                workspace.replaceList(result.list)
            }
        case .fill:
            result = await ArmyListDecisionController.fill(
                workspace: workspace,
                theme: theme,
                decider: decider,
                usedLaya: usedLaya,
                onStep: onStep
            )
        case .fix:
            result = await ArmyListDecisionController.fix(
                workspace: workspace,
                theme: theme,
                decider: decider,
                usedLaya: usedLaya,
                onStep: onStep
            )
        }
        if Task.isCancelled {
            failConstruction("Cancelled.")
            return
        }
        if let result {
            lastConstructionStep = result.steps.last
            finishConstruction(summary: result.summary)
        } else {
            failConstruction("Couldn't finish that construction pass.")
        }
    }

    func beginConstruction(title: String) {
        append(.user, text: title)
        isRunning = true
    }

    func noteConstructionStep(_ step: ArmyListDecisionStep) {
        lastConstructionStep = step
        append(.tool, text: step.applied)
        toolLog.append((name: step.title, detail: step.applied))
    }

    func finishConstruction(summary: String) {
        append(.assistant, text: summary)
        isRunning = false
    }

    func failConstruction(_ message: String) {
        append(.system, text: message)
        isRunning = false
    }

    private func keptListName() -> String? {
        let name = workspace.list.name.trimmingCharacters(in: .whitespacesAndNewlines)
        if name.isEmpty || name == "New list" { return nil }
        return name
    }

    private static let welcomeText =
        "Build, Fill, and Fix pick among legal catalog moves. Theme and Weaknesses use Apple Intelligence when it is available."

    var armyListGateDetail: String {
        switch modelGate {
        case .available:
            return modelGate.detail
        case .needsAppleIntelligence:
            return "Theme and Weaknesses need Apple Intelligence. Build, Fill, and Fix still run."
        case .modelNotReady:
            return "Apple Intelligence is still downloading. Theme and Weaknesses wait; Build, Fill, and Fix still run."
        case .deviceNotEligible:
            return "This hardware does not support Apple Intelligence. Theme and Weaknesses are off; Build, Fill, and Fix still run."
        case .other(let reason):
            return reason
        }
    }
}

private enum ArmyListFMToolBridge {
    static func run(
        _ runtime: ArmyListChatRuntime?,
        name: String,
        work: @escaping @MainActor (ArmyListChatWorkspace) -> String
    ) async throws -> String {
        await Task { @MainActor in
            guard let runtime else {
                return "Army List chat runtime is gone."
            }
            if runtime.mode == .builder {
                runtime.onStarterBuildToolStarted?(name)
            }
            let pending = ArmyListChatEntry(kind: .tool, text: "\(name)…")
            runtime.transcript.append(pending)
            let raw = work(runtime.workspace)
            let label = ArmyListChatToolDisplay.label(name: name, result: raw)
            if let index = runtime.transcript.lastIndex(where: { $0.id == pending.id }) {
                runtime.transcript[index] = ArmyListChatEntry(
                    id: pending.id,
                    kind: .tool,
                    text: label,
                    createdAt: pending.createdAt
                )
            }
            return runtime.noteToolExchange(name: name, result: raw)
        }.value
    }
}

struct ArmyGetListSummaryFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "getListSummary"
    let description = "Return the current roster, points, DP spend, and validation issues."

    @Generable
    struct Arguments {
        @Guide(description: "Unused; pass an empty string")
        var note: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.getListSummary(workspace: workspace)
        }
    }
}

struct ArmySearchCatalogFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "searchCatalog"
    let description = "Search datasheets and detachments by name or keyword. kind: unit, detachment, or any."

    @Generable
    struct Arguments {
        @Guide(description: "Search text, e.g. hearthkyn or brandfast")
        var query: String
        @Guide(description: "unit, detachment, or any")
        var kind: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.searchCatalog(
                workspace: workspace,
                query: arguments.query,
                kind: arguments.kind
            )
        }
    }
}

struct ArmyApplyRosterPlanFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "applyRosterPlan"
    let description = "Replace the whole roster in one call with a battle size, detachments, and units you invented. Prefer this for creative from-scratch builds."

    @Generable
    struct Arguments {
        @Guide(description: "incursion, strike-force, 1000, or 2000")
        var battleSizeID: String
        @Guide(description: "Comma-separated detachment ids/names that fit the DP budget")
        var detachmentIDsCSV: String
        @Guide(description: "Comma-separated datasheet id/name or id:models, e.g. blade-champion:1,custodian-guard:5")
        var unitsCSV: String
        @Guide(description: "Army list name")
        var listName: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.applyRosterPlan(
                workspace: workspace,
                battleSizeID: arguments.battleSizeID,
                detachmentIDsCSV: arguments.detachmentIDsCSV,
                unitsCSV: arguments.unitsCSV,
                listName: arguments.listName
            )
        }
    }
}

struct ArmySetBattleSizeFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "setBattleSize"
    let description = "Set battle size to incursion (1000) or strike-force (2000). Never use this to clear validation errors — fix the roster instead."

    @Generable
    struct Arguments {
        @Guide(description: "incursion, strike-force, 1000, or 2000")
        var battleSizeID: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.setBattleSize(
                workspace: workspace,
                battleSizeID: arguments.battleSizeID
            )
        }
    }
}

struct ArmySetDetachmentsFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "setDetachments"
    let description = "Replace selected detachments. Pass comma-separated detachment ids or names."

    @Generable
    struct Arguments {
        @Guide(description: "Comma-separated detachment ids/names, e.g. brandfast-oathband,farseekers")
        var detachmentIDsCSV: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.setDetachments(
                workspace: workspace,
                detachmentIDsCSV: arguments.detachmentIDsCSV
            )
        }
    }
}

struct ArmyAddUnitFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "addUnit"
    let description = "Add a datasheet to the list. models must be a legal size for that datasheet."

    @Generable
    struct Arguments {
        @Guide(description: "Datasheet id or unique name, e.g. hearthkyn-warriors")
        var datasheetID: String
        @Guide(description: "Model count, e.g. 10")
        var models: Double
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.addUnit(
                workspace: workspace,
                datasheetID: arguments.datasheetID,
                models: arguments.models
            )
        }
    }
}

struct ArmyRemoveUnitFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "removeUnit"
    let description = "Remove a unit instance by UUID from getListSummary / addUnit."

    @Generable
    struct Arguments {
        @Guide(description: "Unit instance UUID")
        var unitID: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.removeUnit(workspace: workspace, unitID: arguments.unitID)
        }
    }
}

struct ArmySetUnitModelsFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "setUnitModels"
    let description = "Change model count on an existing unit UUID."

    @Generable
    struct Arguments {
        @Guide(description: "Unit instance UUID")
        var unitID: String
        @Guide(description: "New model count")
        var models: Double
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.setUnitModels(
                workspace: workspace,
                unitID: arguments.unitID,
                models: arguments.models
            )
        }
    }
}

struct ArmyAttachCharacterFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "attachCharacter"
    let description = "Attach a Leader/Character unit UUID to a bodyguard unit UUID, or bodyUnitID=none to detach."

    @Generable
    struct Arguments {
        @Guide(description: "Character unit UUID")
        var characterUnitID: String
        @Guide(description: "Bodyguard unit UUID, or none")
        var bodyUnitID: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.attachCharacter(
                workspace: workspace,
                characterUnitID: arguments.characterUnitID,
                bodyUnitID: arguments.bodyUnitID
            )
        }
    }
}

struct ArmySetWarlordFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "setWarlord"
    let description = "Set Warlord to a Character unit UUID, or none."

    @Generable
    struct Arguments {
        @Guide(description: "Unit UUID or none")
        var unitID: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.setWarlord(workspace: workspace, unitID: arguments.unitID)
        }
    }
}

struct ArmySetListNameFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "setListName"
    let description = "Rename the army list."

    @Generable
    struct Arguments {
        @Guide(description: "New list name")
        var name: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.setListName(workspace: workspace, name: arguments.name)
        }
    }
}

struct ArmySetEnhancementFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "setEnhancement"
    let description = "Set or clear an enhancement on a unit. Prefer detachmentId--enhancement-slug ids."

    @Generable
    struct Arguments {
        @Guide(description: "Unit instance UUID")
        var unitID: String
        @Guide(description: "Enhancement id, or none to clear")
        var enhancementID: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.setEnhancement(
                workspace: workspace,
                unitID: arguments.unitID,
                enhancementID: arguments.enhancementID
            )
        }
    }
}

struct ArmyClearUnitsFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "clearUnits"
    let description = "Remove every unit from the list (keeps detachments and battle size)."

    @Generable
    struct Arguments {
        @Guide(description: "Unused; pass an empty string")
        var note: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.clearUnits(workspace: workspace)
        }
    }
}
