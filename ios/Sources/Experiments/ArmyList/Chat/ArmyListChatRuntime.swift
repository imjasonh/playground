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
    @Published var transcript: [ArmyListChatEntry] = []
    @Published var isRunning = false
    @Published private(set) var modelGate: AgentModelGate = .unsupportedPlatform

    let workspace: ArmyListChatWorkspace

    private var languageSessionBox: Any?
    private var workspaceBag: AnyCancellable?
    private var carryOverNotes = ""

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
                append(
                    .system,
                    text: "Ask me to build, critique, rename, or fix this list. Every edit is re-checked by the validator."
                )
            }
        }
    }

    func clearTranscript() {
        transcript.removeAll()
        languageSessionBox = nil
        if isModelAvailable {
            append(
                .system,
                text: "Transcript cleared. The list itself is unchanged."
            )
        }
    }

    func send(prompt: String) async {
        let trimmed = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return }
        append(.user, text: trimmed)
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
                        text: "Couldn’t finish after compacting context: \(error.localizedDescription). Try Clear, then Build 1k again (uses seedLegalList in one step)."
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
            return "The on-device model ran out of context while editing. Tap Clear, then Build 1k (one seedLegalList call) or ask for a smaller change."
        }
        return error.localizedDescription
    }

    private func compactLanguageSession(reason: String) {
        languageSessionBox = nil
        append(.system, text: reason)
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
        if isRetryAfterCompact {
            // Carry a tiny roster snapshot into the fresh session instructions
            // so the model knows what survived the compact.
            let summary = workspace.compactSummary(maxIssues: 4)
            carryOverNotes = String(summary.prefix(1_200))
        }
        let session = ensureLanguageSession()
        let response = try await session.respond(to: prompt)
        let text = response.content.trimmingCharacters(in: .whitespacesAndNewlines)
        append(.assistant, text: text.isEmpty ? "(Empty model response.)" : text)
    }

    @available(iOS 26.0, *)
    private func ensureLanguageSession() -> LanguageModelSession {
        if let existing = languageSessionBox as? LanguageModelSession {
            return existing
        }
        var instructions = sessionInstructions
        if !carryOverNotes.isEmpty {
            instructions += "\n\nCurrent list snapshot:\n" + carryOverNotes
            carryOverNotes = ""
        }
        let session = LanguageModelSession(tools: makeFoundationTools(), instructions: instructions)
        languageSessionBox = session
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
        Prefer short replies. For from-scratch 1000/2000 point builds, call seedLegalList once (battleSizeID + optional name). Do not loop addUnit for a full army — that overflows the on-device context window.
        Use searchCatalog before addUnit only for small targeted edits.
        Unit ids in tool results are UUIDs. Pass those UUIDs to removeUnit / attachCharacter / setWarlord / setEnhancement.
        """
    }

    @available(iOS 26.0, *)
    private func makeFoundationTools() -> [any Tool] {
        [
            ArmyGetListSummaryFMTool(runtime: self),
            ArmySearchCatalogFMTool(runtime: self),
            ArmySeedLegalListFMTool(runtime: self),
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
        try await Task { @MainActor in
            guard let runtime else {
                return "Army List chat runtime is gone."
            }
            runtime.transcript.append(
                ArmyListChatEntry(kind: .tool, text: name)
            )
            return work(runtime.workspace)
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
struct ArmySeedLegalListFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "seedLegalList"
    let description = "Replace the roster with a seeded legal list for this faction. Prefer this for from-scratch 1000/2000 point builds instead of many addUnit calls."

    @Generable
    struct Arguments {
        @Guide(description: "incursion, strike-force, 1000, or 2000")
        var battleSizeID: String
        @Guide(description: "Optional army name; empty keeps a generated name")
        var name: String
    }

    func call(arguments: Arguments) async throws -> String {
        try await ArmyListFMToolBridge.run(runtime, name: name) { workspace in
            ArmyListChatToolExecutor.seedLegalList(
                workspace: workspace,
                battleSizeID: arguments.battleSizeID,
                name: arguments.name
            )
        }
    }
}

@available(iOS 26.0, *)
struct ArmySetBattleSizeFMTool: Tool {
    weak var runtime: ArmyListChatRuntime?
    let name = "setBattleSize"
    let description = "Set battle size to incursion (1000) or strike-force (2000)."

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
