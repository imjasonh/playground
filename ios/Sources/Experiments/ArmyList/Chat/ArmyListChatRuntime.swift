import Combine
import Foundation

#if canImport(FoundationModels)
import FoundationModels
#endif

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
    /// How the session is configured. Chat exposes the full tool set for
    /// interactive editing; builder trims to one bulk tool for a self-contained
    /// from-scratch build, which fits the 4096-token window far more reliably
    /// (see the `foundation-models-context` skill).
    enum Mode {
        case chat
        case builder
    }

    /// Rough cost of the army-list tool schemas registered with the session.
    /// Matches `OnDeviceContextManager.safetyBufferTokens` (TN3193 tool + reply headroom).
    static let toolsReserveTokens = OnDeviceContextManager.safetyBufferTokens

    @Published var transcript: [ArmyListChatEntry] = []
    @Published var isRunning = false
    @Published private(set) var modelGate: AgentModelGate = .unsupportedPlatform
    @Published private(set) var contextUsage = AgentContextUsage.empty

    let workspace: ArmyListChatWorkspace
    let mode: Mode

    private var languageSessionBox: Any?
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
        if mode == .chat, isModelAvailable {
            append(
                .system,
                text: "Ask me to build, critique, rename, or fix this list. Every edit is re-checked by the validator."
            )
        }
        publishContextUsage()
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
                append(
                    .system,
                    text: "Ask me to build, critique, rename, or fix this list. Every edit is re-checked by the validator."
                )
            }
        }
    }

    func clearTranscript() {
        transcript.removeAll()
        toolLog.removeAll()
        resetLanguageSession()
        if isModelAvailable {
            append(
                .system,
                text: "Transcript cleared. The list itself is unchanged."
            )
        }
    }

    func send(prompt: String, displayText: String? = nil) async {
        let trimmed = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return }
        let shown = (displayText ?? trimmed).trimmingCharacters(in: .whitespacesAndNewlines)
        append(.user, text: shown.isEmpty ? trimmed : shown)
        isRunning = true
        defer { isRunning = false }

        do {
            #if canImport(FoundationModels)
            if #available(iOS 26.0, *) {
                try await runFoundationModels(prompt: trimmed)
            } else {
                append(.system, text: armyListGateDetail)
            }
            #else
            try await runFoundationModels(prompt: trimmed)
            #endif
        } catch {
            if OnDeviceContextManager.isExceededContextWindow(error) {
                compactLanguageSession(
                    reason: "Model context filled during tool use; compacted and retrying once."
                )
                do {
                    #if canImport(FoundationModels)
                    if #available(iOS 26.0, *) {
                        try await runFoundationModels(prompt: trimmed, isRetryAfterCompact: true)
                        return
                    }
                    #endif
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

    /// FoundationModels often surfaces context overflow as GenerationError code -1
    /// with a generic localizedDescription (no “context” substring).
    nonisolated static func isExceededContextWindow(_ error: Error) -> Bool {
        OnDeviceContextManager.isExceededContextWindow(error)
    }

    private func friendlyGenerationError(_ error: Error) -> String {
        if OnDeviceContextManager.isExceededContextWindow(error) {
            return "The on-device model ran out of context while editing. Tap Clear, then Build 1k again (one applyRosterPlan call) or ask for a smaller change."
        }
        return error.localizedDescription
    }

    private func resetLanguageSession() {
        languageSessionBox = nil
        budget = AgentContextBudget(toolsReserveTokens: Self.toolsReserveTokens)
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
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *),
           let existing = languageSessionBox as? LanguageModelSession,
           let rehydrated = OnDeviceContextManager.rehydratedSession(
               from: existing,
               tools: makeFoundationTools()
           )
        {
            languageSessionBox = rehydrated
            budget = AgentContextBudget(toolsReserveTokens: Self.toolsReserveTokens)
            budget.resetBaseline(
                instructions: sessionInstructions,
                toolsReserveTokens: Self.toolsReserveTokens
            )
            budget.addText(carryOverNotes)
        } else {
            languageSessionBox = nil
            budget = AgentContextBudget(toolsReserveTokens: Self.toolsReserveTokens)
        }
        #else
        languageSessionBox = nil
        budget = AgentContextBudget(toolsReserveTokens: Self.toolsReserveTokens)
        #endif
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
        var instructions = sessionInstructions
        if !carryOverNotes.isEmpty {
            instructions += "\n\n" + carryOverNotes
            carryOverNotes = ""
        }
        let session = LanguageModelSession(tools: makeFoundationTools(), instructions: instructions)
        languageSessionBox = session
        budget.resetBaseline(
            instructions: instructions,
            toolsReserveTokens: Self.toolsReserveTokens
        )
        publishContextUsage()
        return session
    }

    @available(iOS 26.0, *)
    private var sessionInstructions: String {
        if mode == .builder {
            return builderInstructions
        }
        return chatInstructions
    }

    /// Short instructions for a one-shot from-scratch build. The prompt carries
    /// the faction, points limit, DP budget, and valid ids, so the model needs
    /// only one `applyRosterPlan` call — keeping the 4096-token window clear.
    @available(iOS 26.0, *)
    private var builderInstructions: String {
        """
        You build exactly one Warhammer 40,000 army list, then stop.
        The user message lists the faction, points limit, DP budget, valid detachment ids, and valid unit ids with points.
        Call applyRosterPlan exactly once, using only ids from that message: one detachment within the DP budget and units totaling as close to the points limit as possible without exceeding it (aim to leave at most ~25 pts unused).
        Honor any Theme line in the user message when picking units and the list name.
        Include at least one Character so the list has a Warlord. Give the list a short themed name.
        Do not call any other tool and do not write prose.
        """
    }

    @available(iOS 26.0, *)
    private var chatInstructions: String {
        """
        You help the user build and discuss a Warhammer 40,000 11th Edition army list inside the Playground app.
        Faction for this list is fixed to whatever getListSummary reports. Do not switch factions.
        Construction facts (points, Detachment Points, join edges, legality) come ONLY from tools. Never invent datasheet ids or points.
        After mutating tools, read the returned Status line. If ILLEGAL, keep fixing with tools or explain what is still wrong.
        For thematic questions (army name, color scheme, lore vibe, matchup opinions), answer helpfully and label opinions as opinions.
        Prefer short replies. Format with Markdown: put a blank line between paragraphs and between matchup/section blocks, use **bold** for headings, and put each Weakness / Countermeasure on its own line. Never run sections together on one line.
        Always answer the latest user message; do not keep talking about an earlier Theme/name request unless they ask again.
        For from-scratch 1000/2000 point builds: invent a fresh theme each time (different units/detachment/name), call searchCatalog as needed, then applyRosterPlan once with your full plan spending as close to the points limit as possible. Do not loop addUnit for a full army — that overflows the on-device context window.
        When fixing errors: keep the current battle size (never call setBattleSize). Prefer removeUnit / setUnitModels / setDetachments / setWarlord / attachCharacter. Respect datasheet duplicate limits for this battle size — addUnit rejects illegal copies.
        When filling points: keep battle size and existing units; add thematic units until remaining points cannot fit another legal datasheet (aim to leave at most ~25 pts unused). Re-read Status after each mutation.
        Use addUnit only for small targeted edits after a roster already exists.
        Unit ids in tool results are UUIDs. Pass those UUIDs to removeUnit / attachCharacter / setWarlord / setEnhancement.
        """
    }

    @available(iOS 26.0, *)
    private func makeFoundationTools() -> [any Tool] {
        // A from-scratch build only needs the bulk roster tool. Fewer resident
        // tool schemas leave far more of the 4096-token window for the plan.
        if mode == .builder {
            return [ArmyApplyRosterPlanFMTool(runtime: self)]
        }
        return [
            ArmyGetListSummaryFMTool(runtime: self),
            ArmySearchCatalogFMTool(runtime: self),
            ArmyApplyRosterPlanFMTool(runtime: self),
            ArmySetBattleSizeFMTool(runtime: self),
            ArmySetDetachmentsFMTool(runtime: self),
            ArmyAddUnitFMTool(runtime: self),
            ArmyRemoveUnitFMTool(runtime: self),
            ArmySetUnitModelsFMTool(runtime: self),
            ArmyAttachCharacterFMTool(runtime: self),
            ArmySetWarlordFMTool(runtime: self),
            ArmySetListNameFMTool(runtime: self),
            ArmySetEnhancementFMTool(runtime: self),
            ArmyClearUnitsFMTool(runtime: self),
        ]
    }
    #else
    private func runFoundationModels(prompt: String, isRetryAfterCompact: Bool = false) async throws {
        _ = prompt
        _ = isRetryAfterCompact
        append(.system, text: armyListGateDetail)
    }
    #endif

    var armyListGateDetail: String {
        switch modelGate {
        case .available:
            return modelGate.detail
        case .needsAppleIntelligence:
            return "Army List chat uses the on-device model. Turn on Apple Intelligence in Settings, then come back."
        case .modelNotReady:
            return "Apple Intelligence is on, but the on-device model is still downloading. Check again when it finishes."
        case .deviceNotEligible:
            return "This hardware doesn’t support Apple Intelligence, so Army List chat can’t run here. Authoring and validation still work."
        case .unsupportedPlatform:
            return "Army List chat needs iOS 26+ with Apple Intelligence. Authoring and validation still work without it."
        case .other(let reason):
            return reason
        }
    }
}

#if canImport(FoundationModels)
@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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

@available(iOS 26.0, *)
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
#endif
