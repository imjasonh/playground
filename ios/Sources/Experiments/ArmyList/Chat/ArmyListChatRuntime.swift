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
    /// Rough cost of the army-list tool schemas registered with the session.
    static let toolsReserveTokens = 1_500

    @Published var transcript: [ArmyListChatEntry] = []
    @Published var isRunning = false
    @Published private(set) var modelGate: AgentModelGate = .unsupportedPlatform
    @Published private(set) var contextUsage = AgentContextUsage.empty

    let workspace: ArmyListChatWorkspace

    private var languageSessionBox: Any?
    private var workspaceBag: AnyCancellable?
    private var carryOverNotes = ""
    private var budget = AgentContextBudget(toolsReserveTokens: ArmyListChatRuntime.toolsReserveTokens)
    private var didCompactThisSession = false
    /// Full tool payloads for export (may be longer than what the model received).
    private(set) var toolLog: [(name: String, detail: String)] = []

    var isModelAvailable: Bool { modelGate.isAvailable }

    init(workspace: ArmyListChatWorkspace) {
        self.workspace = workspace
        workspaceBag = workspace.objectWillChange.sink { [weak self] _ in
            self?.objectWillChange.send()
        }
        refreshModelStatus()
        if isModelAvailable {
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
            if Self.isExceededContextWindow(error) {
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
        let text = error.localizedDescription.lowercased()
        if text.contains("context window")
            || text.contains("exceededcontext")
            || text.contains("contextsizeexceeded")
        {
            return true
        }
        let ns = error as NSError
        let domain = ns.domain.lowercased()
        if domain.contains("foundationmodels") {
            if text.contains("context") { return true }
            // Observed on device: GenerationError error -1 with no useful message.
            if ns.code == -1 { return true }
        }
        return false
    }

    private func friendlyGenerationError(_ error: Error) -> String {
        if Self.isExceededContextWindow(error) {
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
        languageSessionBox = nil
        budget = AgentContextBudget(toolsReserveTokens: Self.toolsReserveTokens)
        append(.system, text: reason)
        publishContextUsage()
    }

    /// Fresh-session notes after compact so follow-ups keep list + recent turns.
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
        let recent = transcript.filter { entry in
            switch entry.kind {
            case .user, .assistant: return true
            case .system, .tool: return false
            }
        }.suffix(4)
        if !recent.isEmpty {
            parts.append("Recent chat (oldest first):")
            for entry in recent {
                let who = entry.kind == .user ? "User" : "Assistant"
                let body = entry.text
                    .replacingOccurrences(of: "\n", with: " ")
                    .trimmingCharacters(in: .whitespacesAndNewlines)
                parts.append("\(who): \(String(body.prefix(280)))")
            }
        }
        return AgentContextBudget.truncateToChars(parts.joined(separator: "\n"), maxChars: 1_400)
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
        """
        You help the user build and discuss a Warhammer 40,000 11th Edition army list inside the Playground app.
        Faction for this list is fixed to whatever getListSummary reports. Do not switch factions.
        Construction facts (points, Detachment Points, join edges, legality) come ONLY from tools. Never invent datasheet ids or points.
        After mutating tools, read the returned Status line. If ILLEGAL, keep fixing with tools or explain what is still wrong.
        For thematic questions (army name, color scheme, lore vibe, matchup opinions), answer helpfully and label opinions as opinions.
        Prefer short replies. Format with Markdown (bold, bullets, short headings) when it helps scanability.
        Always answer the latest user message; do not keep talking about an earlier Theme/name request unless they ask again.
        For from-scratch builds within the current battle size: invent a fresh theme, call searchCatalog as needed, then applyRosterPlan once. Do not loop addUnit for a full army — that overflows the on-device context window.
        Battle size is fixed in chat — the user sets it at create time or in the editor. Never invent a different points level.
        When fixing errors: Prefer removeUnit / setUnitModels / setDetachments / setWarlord / attachCharacter. Respect datasheet duplicate limits for this battle size — addUnit rejects illegal copies.
        When filling points: keep existing units; add a few thematic units that fit remaining points without exceeding duplicate caps. Re-read Status after each mutation.
        Use addUnit only for small targeted edits after a roster already exists.
        Unit ids in tool results are UUIDs. Pass those UUIDs to removeUnit / attachCharacter / setWarlord / setEnhancement.
        """
    }

    @available(iOS 26.0, *)
    private func makeFoundationTools() -> [any Tool] {
        [
            ArmyGetListSummaryFMTool(runtime: self),
            ArmySearchCatalogFMTool(runtime: self),
            ArmyApplyRosterPlanFMTool(runtime: self),
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
        try await Task { @MainActor in
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
    let description = "Replace the whole roster in one call with detachments and units you invented. Keeps the list's current battle size."

    @Generable
    struct Arguments {
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
                detachmentIDsCSV: arguments.detachmentIDsCSV,
                unitsCSV: arguments.unitsCSV,
                listName: arguments.listName
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
