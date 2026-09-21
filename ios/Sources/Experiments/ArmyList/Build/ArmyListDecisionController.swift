import Foundation

/// One Laya (or greedy) pick the construction loop applied.
struct ArmyListDecisionStep: Identifiable, Equatable {
    let id: UUID
    let title: String
    let instructions: String
    let decision: LayaDecision
    let applied: String

    init(
        id: UUID = UUID(),
        title: String,
        instructions: String,
        decision: LayaDecision,
        applied: String
    ) {
        self.id = id
        self.title = title
        self.instructions = instructions
        self.decision = decision
        self.applied = applied
    }
}

/// Roster plus the typed decisions that produced it.
struct ArmyListConstructionResult: Equatable {
    var list: ArmyListDocument
    var steps: [ArmyListDecisionStep]
    var usedLaya: Bool
    var summary: String
}

/// Builds, fills, and repairs lists by asking ``LayaDeciding`` to pick among
/// legal catalog moves. Swift applies the pick through
/// ``ArmyListChatToolExecutor`` and ``ArmyListValidator``.
@MainActor
enum ArmyListDecisionController {
    /// Laya when the shared graph is loaded; otherwise the first-option greedy
    /// decider (options are already ranked).
    static func activeDecider(store: LayaModelStore = .shared) -> any LayaDeciding {
        store.isReady ? store : LayaGreedyDecider()
    }

    static func usedLaya(store: LayaModelStore = .shared) -> Bool {
        store.isReady
    }

    static func build(
        catalog: ArmyCatalog,
        factionID: String,
        battleSizeID: String,
        theme: String,
        userName: String?,
        decider: any LayaDeciding,
        usedLaya: Bool = false,
        onPhase: (@MainActor (ArmyListStarterBuildProgress.Phase) -> Void)? = nil,
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)? = nil
    ) async -> ArmyListConstructionResult? {
        if Task.isCancelled { return nil }
        if ArmyListStarterPrompt.buildFeasibilityIssue(
            catalog: catalog,
            factionID: factionID,
            battleSizeID: battleSizeID
        ) != nil {
            return nil
        }
        let name = listName(
            catalog: catalog,
            factionID: factionID,
            battleSizeID: battleSizeID,
            theme: theme,
            userName: userName
        )
        var list = ArmyListDocument(
            name: name,
            catalogVersion: catalog.version,
            factionID: factionID,
            battleSizeID: battleSizeID
        )
        let workspace = ArmyListChatWorkspace(list: list, catalog: catalog)
        var steps: [ArmyListDecisionStep] = []

        onPhase?(.choosingDetachment)
        guard await pickDetachments(
            workspace: workspace,
            theme: theme,
            decider: decider,
            steps: &steps,
            onStep: onStep
        ) else { return nil }

        onPhase?(.addingUnits)
        guard await addUnits(
            workspace: workspace,
            theme: theme,
            decider: decider,
            steps: &steps,
            onStep: onStep
        ) else { return nil }

        onPhase?(.attaching)
        guard await assignWarlord(
            workspace: workspace,
            theme: theme,
            decider: decider,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        guard await attachLeaders(
            workspace: workspace,
            theme: theme,
            decider: decider,
            steps: &steps,
            onStep: onStep
        ) else { return nil }

        if Task.isCancelled { return nil }
        list = workspace.list
        if let userName, !userName.isEmpty {
            list.name = userName
            workspace.replaceList(list)
        }
        return ArmyListConstructionResult(
            list: workspace.list,
            steps: steps,
            usedLaya: usedLaya,
            summary: summary(workspace: workspace, action: "Built")
        )
    }

    static func fill(
        workspace: ArmyListChatWorkspace,
        theme: String,
        decider: any LayaDeciding,
        usedLaya: Bool = false,
        onPhase: (@MainActor (ArmyListStarterBuildProgress.Phase) -> Void)? = nil,
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)? = nil
    ) async -> ArmyListConstructionResult? {
        if Task.isCancelled { return nil }
        var steps: [ArmyListDecisionStep] = []
        if workspace.list.detachmentIDs.isEmpty {
            onPhase?(.choosingDetachment)
            guard await pickDetachments(
                workspace: workspace,
                theme: theme,
                decider: decider,
                steps: &steps,
                onStep: onStep
            ) else { return nil }
        }
        onPhase?(.addingUnits)
        guard await addUnits(
            workspace: workspace,
            theme: theme,
            decider: decider,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        onPhase?(.attaching)
        guard await assignWarlord(
            workspace: workspace,
            theme: theme,
            decider: decider,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        guard await attachLeaders(
            workspace: workspace,
            theme: theme,
            decider: decider,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        if Task.isCancelled { return nil }
        return ArmyListConstructionResult(
            list: workspace.list,
            steps: steps,
            usedLaya: usedLaya,
            summary: summary(workspace: workspace, action: "Filled")
        )
    }

    static func fix(
        workspace: ArmyListChatWorkspace,
        theme: String,
        decider: any LayaDeciding,
        usedLaya: Bool = false,
        onPhase: (@MainActor (ArmyListStarterBuildProgress.Phase) -> Void)? = nil,
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)? = nil
    ) async -> ArmyListConstructionResult? {
        if Task.isCancelled { return nil }
        var steps: [ArmyListDecisionStep] = []
        onPhase?(.attaching)
        for _ in 0..<8 {
            if Task.isCancelled { return nil }
            let errors = workspace.validation.errors
            if errors.isEmpty { break }
            let repaired = await repair(
                error: errors[0],
                workspace: workspace,
                theme: theme,
                decider: decider,
                steps: &steps,
                onStep: onStep
            )
            if !repaired { break }
        }
        if Task.isCancelled { return nil }
        return ArmyListConstructionResult(
            list: workspace.list,
            steps: steps,
            usedLaya: usedLaya,
            summary: summary(workspace: workspace, action: "Repaired")
        )
    }

    // MARK: - Steps

    private static func pickDetachments(
        workspace: ArmyListChatWorkspace,
        theme: String,
        decider: any LayaDeciding,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        if Task.isCancelled { return false }
        guard let battle = workspace.catalog.battleSize(id: workspace.list.battleSizeID) else {
            return false
        }
        let candidates = ArmyListPalette.legalDetachments(
            catalog: workspace.catalog,
            factionID: workspace.list.factionID,
            dpBudget: battle.detachmentPointsBudget,
            theme: theme
        )
        if candidates.isEmpty { return false }
        let shortlist = Array(candidates.prefix(ArmyListPalette.maxLayaOptions))
        let options = shortlist.map { LayaChoiceOption($0.name, "\($0.detachmentPoints) DP") }
        let instructions = "Pick a detachment"
        let decision = await decide(
            decider: decider,
            state: ArmyListLayaSnapshot.text(list: workspace.list, catalog: workspace.catalog, theme: theme),
            question: .choice(instructions: instructions, options: options)
        )
        let picked = shortlist.first { $0.name == decision.choiceLabel } ?? shortlist[0]
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: picked.id
        )
        record(
            title: "Detachment",
            instructions: instructions,
            decision: decision,
            applied: "Detachment \(picked.name)",
            steps: &steps,
            onStep: onStep
        )

        let spent = workspace.catalog.detachment(id: picked.id)?.detachmentPoints ?? picked.detachmentPoints
        let leftover = battle.detachmentPointsBudget - spent
        let extras = candidates.filter { $0.id != picked.id && $0.detachmentPoints <= leftover }
        if leftover > 0, !extras.isEmpty {
            if Task.isCancelled { return false }
            let extraList = Array(extras.prefix(ArmyListPalette.maxLayaOptions - 1))
            var extraOptions = [LayaChoiceOption("none", "keep one detachment")]
            extraOptions.append(contentsOf: extraList.map { LayaChoiceOption($0.name, "\($0.detachmentPoints) DP") })
            let extraDecision = await decide(
                decider: decider,
                state: ArmyListLayaSnapshot.text(list: workspace.list, catalog: workspace.catalog, theme: theme),
                question: .choice(instructions: "Add a second detachment", options: extraOptions)
            )
            if let extra = extraList.first(where: { $0.name == extraDecision.choiceLabel }) {
                _ = ArmyListChatToolExecutor.setDetachments(
                    workspace: workspace,
                    detachmentIDsCSV: "\(picked.id),\(extra.id)"
                )
                record(
                    title: "Detachment",
                    instructions: "Add a second detachment",
                    decision: extraDecision,
                    applied: "Also \(extra.name)",
                    steps: &steps,
                    onStep: onStep
                )
            } else {
                record(
                    title: "Detachment",
                    instructions: "Add a second detachment",
                    decision: extraDecision,
                    applied: "One detachment",
                    steps: &steps,
                    onStep: onStep
                )
            }
        }
        return !Task.isCancelled
    }

    private static func addUnits(
        workspace: ArmyListChatWorkspace,
        theme: String,
        decider: any LayaDeciding,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        guard let battle = workspace.catalog.battleSize(id: workspace.list.battleSizeID) else {
            return false
        }
        for _ in 0..<ArmyListPalette.maxAddSteps {
            if Task.isCancelled { return false }
            let remaining = battle.pointsLimit - workspace.validation.totalPoints
            let hasCharacter = ArmyListPalette.hasCharacter(list: workspace.list, catalog: workspace.catalog)
            if hasCharacter, remaining <= ArmyListPalette.goodEnoughSlack {
                return true
            }
            if let cheapest = ArmyListPalette.cheapestLegalAdd(
                catalog: workspace.catalog,
                list: workspace.list,
                remainingPoints: remaining
            ), remaining < cheapest {
                return true
            }
            var moves = ArmyListPalette.legalAdds(
                catalog: workspace.catalog,
                list: workspace.list,
                theme: theme,
                remainingPoints: remaining,
                hasCharacter: hasCharacter,
                charactersOnly: !hasCharacter
            )
            if moves.isEmpty, !hasCharacter {
                moves = ArmyListPalette.legalAdds(
                    catalog: workspace.catalog,
                    list: workspace.list,
                    theme: theme,
                    remainingPoints: remaining,
                    hasCharacter: hasCharacter,
                    charactersOnly: false
                )
            }
            if moves.isEmpty { return true }

            let instructions = hasCharacter ? "Add one unit" : "Add a Character"
            let decision = await decide(
                decider: decider,
                state: ArmyListLayaSnapshot.text(
                    list: workspace.list,
                    catalog: workspace.catalog,
                    theme: theme,
                    validation: workspace.validation
                ),
                question: .choice(instructions: instructions, options: moves.map { $0.option() })
            )
            if decision.actProbability < 0.35, hasCharacter, remaining <= 80 {
                record(
                    title: "Add unit",
                    instructions: instructions,
                    decision: decision,
                    applied: "Stopped adding",
                    steps: &steps,
                    onStep: onStep
                )
                return true
            }
            let move = moves.first { $0.label == decision.choiceLabel } ?? moves[0]
            let output = ArmyListChatToolExecutor.addUnit(
                workspace: workspace,
                datasheetID: move.sheet.id,
                models: Double(move.models)
            )
            if output.hasPrefix("Rejected:") {
                record(
                    title: "Add unit",
                    instructions: instructions,
                    decision: decision,
                    applied: "Skipped \(move.sheet.name)",
                    steps: &steps,
                    onStep: onStep
                )
                return true
            }
            record(
                title: "Add unit",
                instructions: instructions,
                decision: decision,
                applied: "Added \(move.sheet.name)×\(move.models)",
                steps: &steps,
                onStep: onStep
            )
        }
        return !Task.isCancelled
    }

    private static func assignWarlord(
        workspace: ArmyListChatWorkspace,
        theme: String,
        decider: any LayaDeciding,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        if Task.isCancelled { return false }
        let characters = ArmyListPalette.characters(on: workspace.list, catalog: workspace.catalog)
        if characters.isEmpty { return true }
        if characters.count == 1 {
            if workspace.list.warlordUnitID != characters[0].id {
                _ = ArmyListChatToolExecutor.setWarlord(
                    workspace: workspace,
                    unitID: characters[0].id.uuidString
                )
            }
            return true
        }
        let options = characters.prefix(ArmyListPalette.maxLayaOptions).map { unit in
            let name = workspace.catalog.datasheet(id: unit.datasheetID)?.name ?? unit.datasheetID
            return LayaChoiceOption(name)
        }
        let shortlist = Array(characters.prefix(ArmyListPalette.maxLayaOptions))
        let instructions = "Pick the Warlord"
        let decision = await decide(
            decider: decider,
            state: ArmyListLayaSnapshot.text(list: workspace.list, catalog: workspace.catalog, theme: theme),
            question: .choice(instructions: instructions, options: options)
        )
        let picked = shortlist.first {
            (workspace.catalog.datasheet(id: $0.datasheetID)?.name ?? $0.datasheetID) == decision.choiceLabel
        } ?? shortlist[0]
        _ = ArmyListChatToolExecutor.setWarlord(workspace: workspace, unitID: picked.id.uuidString)
        let name = workspace.catalog.datasheet(id: picked.datasheetID)?.name ?? picked.datasheetID
        record(
            title: "Warlord",
            instructions: instructions,
            decision: decision,
            applied: "Warlord \(name)",
            steps: &steps,
            onStep: onStep
        )
        return true
    }

    private static func attachLeaders(
        workspace: ArmyListChatWorkspace,
        theme: String,
        decider: any LayaDeciding,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        let leaders = workspace.list.units.filter { unit in
            guard let sheet = workspace.catalog.datasheet(id: unit.datasheetID) else { return false }
            return sheet.characterRole != nil && unit.attachedToUnitID == nil && !sheet.leaderTo.isEmpty
        }
        for character in leaders {
            if Task.isCancelled { return false }
            guard let sheet = workspace.catalog.datasheet(id: character.datasheetID) else { continue }
            let bodies = ArmyListPalette.legalBodyguards(
                catalog: workspace.catalog,
                list: workspace.list,
                characterSheet: sheet
            )
            if bodies.isEmpty {
                if sheet.mustAttach {
                    _ = ArmyListChatToolExecutor.removeUnit(
                        workspace: workspace,
                        unitID: character.id.uuidString
                    )
                    let drop = LayaGreedyDecider.choice(
                        label: "remove",
                        options: [LayaChoiceOption("remove")],
                        act: 1
                    )
                    record(
                        title: "Attach",
                        instructions: "No bodyguard",
                        decision: drop,
                        applied: "Removed \(sheet.name)",
                        steps: &steps,
                        onStep: onStep
                    )
                }
                continue
            }
            if bodies.count == 1 {
                _ = ArmyListChatToolExecutor.attachCharacter(
                    workspace: workspace,
                    characterUnitID: character.id.uuidString,
                    bodyUnitID: bodies[0].id.uuidString
                )
                let bodyName = workspace.catalog.datasheet(id: bodies[0].datasheetID)?.name ?? bodies[0].datasheetID
                let decision = LayaGreedyDecider.choice(
                    label: bodyName,
                    options: [LayaChoiceOption(bodyName)],
                    act: 1
                )
                record(
                    title: "Attach",
                    instructions: "Attach \(sheet.name)",
                    decision: decision,
                    applied: "Attached \(sheet.name) to \(bodyName)",
                    steps: &steps,
                    onStep: onStep
                )
                continue
            }
            var options: [LayaChoiceOption] = []
            if !sheet.mustAttach {
                options.append(LayaChoiceOption("none", "leave unattached"))
            }
            let bodySlice = Array(bodies.prefix(ArmyListPalette.maxLayaOptions - options.count))
            options.append(contentsOf: bodySlice.map { body in
                let name = workspace.catalog.datasheet(id: body.datasheetID)?.name ?? body.datasheetID
                return LayaChoiceOption(name)
            })
            let instructions = "Attach \(sheet.name)"
            let decision = await decide(
                decider: decider,
                state: ArmyListLayaSnapshot.text(list: workspace.list, catalog: workspace.catalog, theme: theme),
                question: .choice(instructions: instructions, options: options)
            )
            if decision.choiceLabel == "none" {
                record(
                    title: "Attach",
                    instructions: instructions,
                    decision: decision,
                    applied: "Left \(sheet.name) unattached",
                    steps: &steps,
                    onStep: onStep
                )
                continue
            }
            let body = bodySlice.first {
                (workspace.catalog.datasheet(id: $0.datasheetID)?.name ?? $0.datasheetID) == decision.choiceLabel
            } ?? bodySlice[0]
            _ = ArmyListChatToolExecutor.attachCharacter(
                workspace: workspace,
                characterUnitID: character.id.uuidString,
                bodyUnitID: body.id.uuidString
            )
            let bodyName = workspace.catalog.datasheet(id: body.datasheetID)?.name ?? body.datasheetID
            record(
                title: "Attach",
                instructions: instructions,
                decision: decision,
                applied: "Attached \(sheet.name) to \(bodyName)",
                steps: &steps,
                onStep: onStep
            )
        }
        return !Task.isCancelled
    }

    private static func repair(
        error: ValidationIssue,
        workspace: ArmyListChatWorkspace,
        theme: String,
        decider: any LayaDeciding,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        switch error.code {
        case "warlord.missing":
            return await assignWarlord(
                workspace: workspace,
                theme: theme,
                decider: decider,
                steps: &steps,
                onStep: onStep
            )
        case "detachment.required":
            return await pickDetachments(
                workspace: workspace,
                theme: theme,
                decider: decider,
                steps: &steps,
                onStep: onStep
            )
        case "unit.mustAttach":
            return await attachLeaders(
                workspace: workspace,
                theme: theme,
                decider: decider,
                steps: &steps,
                onStep: onStep
            )
        case "unit.attachIllegal", "unit.attachMissing", "unit.attachSelf",
             "unit.attachNotCharacter", "unit.attachNoTargets":
            if let unitID = error.unitID {
                _ = ArmyListChatToolExecutor.attachCharacter(
                    workspace: workspace,
                    characterUnitID: unitID.uuidString,
                    bodyUnitID: "none"
                )
                let decision = LayaGreedyDecider.choice(
                    label: "none",
                    options: [LayaChoiceOption("none")],
                    act: 1
                )
                record(
                    title: "Attach",
                    instructions: "Clear bad attach",
                    decision: decision,
                    applied: "Detached unit",
                    steps: &steps,
                    onStep: onStep
                )
            }
            return true
        case "points.overLimit":
            return await cutForPoints(
                workspace: workspace,
                theme: theme,
                decider: decider,
                steps: &steps,
                onStep: onStep
            )
        case "unit.duplicateCap", "unit.epicHeroDuplicate":
            return removeExtraCopy(workspace: workspace, steps: &steps, onStep: onStep)
        case "dp.overBudget":
            if workspace.list.detachmentIDs.count > 1 {
                var ids = workspace.list.detachmentIDs
                ids.removeLast()
                _ = ArmyListChatToolExecutor.setDetachments(
                    workspace: workspace,
                    detachmentIDsCSV: ids.joined(separator: ",")
                )
                let decision = LayaGreedyDecider.choice(
                    label: "drop",
                    options: [LayaChoiceOption("drop")],
                    act: 1
                )
                record(
                    title: "Detachment",
                    instructions: "Drop a detachment",
                    decision: decision,
                    applied: "Dropped last detachment",
                    steps: &steps,
                    onStep: onStep
                )
                return true
            }
            return false
        case "list.empty":
            return await addUnits(
                workspace: workspace,
                theme: theme,
                decider: decider,
                steps: &steps,
                onStep: onStep
            )
        default:
            return false
        }
    }

    private static func cutForPoints(
        workspace: ArmyListChatWorkspace,
        theme: String,
        decider: any LayaDeciding,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        let warlord = workspace.list.warlordUnitID
        let removable = workspace.list.units.filter { unit in
            if let warlord, unit.id == warlord { return false }
            return true
        }
        if removable.isEmpty { return false }
        let slice = Array(removable.suffix(ArmyListPalette.maxLayaOptions))
        let options = slice.map { unit -> LayaChoiceOption in
            let name = workspace.catalog.datasheet(id: unit.datasheetID)?.name ?? unit.datasheetID
            return LayaChoiceOption(name)
        }
        let instructions = "Drop a unit"
        let decision = await decide(
            decider: decider,
            state: ArmyListLayaSnapshot.text(
                list: workspace.list,
                catalog: workspace.catalog,
                theme: theme,
                validation: workspace.validation
            ),
            question: .choice(instructions: instructions, options: options)
        )
        let picked = slice.first {
            (workspace.catalog.datasheet(id: $0.datasheetID)?.name ?? $0.datasheetID) == decision.choiceLabel
        } ?? slice[0]
        let name = workspace.catalog.datasheet(id: picked.datasheetID)?.name ?? picked.datasheetID
        _ = ArmyListChatToolExecutor.removeUnit(workspace: workspace, unitID: picked.id.uuidString)
        record(
            title: "Cut",
            instructions: instructions,
            decision: decision,
            applied: "Removed \(name)",
            steps: &steps,
            onStep: onStep
        )
        return true
    }

    private static func removeExtraCopy(
        workspace: ArmyListChatWorkspace,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) -> Bool {
        let counts = Dictionary(grouping: workspace.list.units, by: \.datasheetID)
        guard let over = counts.first(where: { $0.value.count > 1 }) else { return false }
        let victim = over.value.last!
        let name = workspace.catalog.datasheet(id: victim.datasheetID)?.name ?? victim.datasheetID
        _ = ArmyListChatToolExecutor.removeUnit(workspace: workspace, unitID: victim.id.uuidString)
        let decision = LayaGreedyDecider.choice(
            label: name,
            options: [LayaChoiceOption(name)],
            act: 1
        )
        var local = steps
        record(
            title: "Cut",
            instructions: "Remove extra copy",
            decision: decision,
            applied: "Removed extra \(name)",
            steps: &local,
            onStep: onStep
        )
        steps = local
        return true
    }

    // MARK: - Helpers

    private static func decide(
        decider: any LayaDeciding,
        state: String,
        question: LayaQuestion
    ) async -> LayaDecision {
        do {
            return try await decider.decide(state: state, question: question)
        } catch {
            return (try? await LayaGreedyDecider().decide(state: state, question: question))
                ?? LayaDecision(
                    kind: question.kind,
                    answer: .noul(probability: 0),
                    confidence: 0,
                    actProbability: 0
                )
        }
    }

    private static func record(
        title: String,
        instructions: String,
        decision: LayaDecision,
        applied: String,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) {
        let step = ArmyListDecisionStep(
            title: title,
            instructions: instructions,
            decision: decision,
            applied: applied
        )
        steps.append(step)
        onStep?(step)
    }

    static func listName(
        catalog: ArmyCatalog,
        factionID: String,
        battleSizeID: String,
        theme: String,
        userName: String?
    ) -> String {
        if let userName {
            let trimmed = userName.trimmingCharacters(in: .whitespacesAndNewlines)
            if !trimmed.isEmpty { return trimmed }
        }
        let faction = catalog.faction(id: factionID)?.name ?? factionID
        let themeBit = theme.trimmingCharacters(in: .whitespacesAndNewlines)
        if !themeBit.isEmpty {
            return "\(faction) \(themeBit)"
        }
        let battle = catalog.battleSize(id: battleSizeID)?.name ?? battleSizeID
        return "\(faction) \(battle)"
    }

    private static func summary(workspace: ArmyListChatWorkspace, action: String) -> String {
        let result = workspace.validation
        let limit = workspace.catalog.battleSize(id: workspace.list.battleSizeID)?.pointsLimit ?? 0
        let legal = result.isLegal ? "Legal" : "Illegal"
        return "\(action) \(workspace.list.name): \(result.totalPoints)/\(limit) pts, \(legal), \(workspace.list.units.count) units."
    }
}
