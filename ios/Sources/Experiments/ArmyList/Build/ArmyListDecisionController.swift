import Foundation

/// One construction step the harness applied, tagged with the worker that
/// answered.
struct ArmyListDecisionStep: Identifiable, Equatable {
    let id: UUID
    let title: String
    let instructions: String
    let decision: LayaDecision
    let applied: String
    let worker: ArmyListHarness.Worker

    init(
        id: UUID = UUID(),
        title: String,
        instructions: String,
        decision: LayaDecision,
        applied: String,
        worker: ArmyListHarness.Worker
    ) {
        self.id = id
        self.title = title
        self.instructions = instructions
        self.decision = decision
        self.applied = applied
        self.worker = worker
    }
}

/// Roster plus the typed decisions that produced it.
struct ArmyListConstructionResult: Equatable {
    var list: ArmyListDocument
    var steps: [ArmyListDecisionStep]
    var usedLaya: Bool
    var summary: String
    var themeBrief: ArmyListThemeBrief
    var themeScoreLabel: String?
}

/// Construction harness. Mechanical catalog code lists legal moves and applies
/// picks. Laya answers choices, leftover yes/no, and a theme score. Apple
/// Intelligence writes the theme brief and a list name once. Workers do not
/// call each other.
@MainActor
enum ArmyListDecisionController {
    /// Laya when the shared graph is loaded; otherwise the first-option greedy
    /// decider (options are already ranked).
    static func activeDecider(store: LayaModelStore? = nil) -> any LayaDeciding {
        let store = store ?? LayaModelStore.shared
        return store.isReady ? store : LayaGreedyDecider()
    }

    static func usedLaya(store: LayaModelStore? = nil) -> Bool {
        (store ?? LayaModelStore.shared).isReady
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
        var list = ArmyListDocument(
            name: "New list",
            catalogVersion: catalog.version,
            factionID: factionID,
            battleSizeID: battleSizeID
        )
        var steps: [ArmyListDecisionStep] = []
        let brief = await ArmyListThemeBriefBuilder.make(
            catalog: catalog,
            factionID: factionID,
            prompt: theme,
            list: list
        )
        if Task.isCancelled { return nil }
        recordThemeBrief(brief: brief, steps: &steps, onStep: onStep)
        list.name = listName(
            catalog: catalog,
            factionID: factionID,
            battleSizeID: battleSizeID,
            theme: theme,
            userName: userName,
            brief: brief
        )
        let workspace = ArmyListChatWorkspace(list: list, catalog: catalog)

        onPhase?(.choosingDetachment)
        guard await pickDetachments(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }

        onPhase?(.addingUnits)
        guard await addUnits(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }

        onPhase?(.attaching)
        guard await assignWarlord(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        guard await attachLeaders(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }

        onPhase?(.assigningEnhancements)
        guard await assignEnhancements(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        guard await packRemaining(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }

        if Task.isCancelled { return nil }
        list = workspace.list
        if let userName, !userName.isEmpty {
            list.name = userName
            workspace.replaceList(list)
        }
        return await finish(
            workspace: workspace,
            action: "Built",
            brief: brief,
            usedLaya: usedLaya,
            decider: decider,
            steps: &steps,
            onStep: onStep
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
        let brief = await ArmyListThemeBriefBuilder.make(
            catalog: workspace.catalog,
            factionID: workspace.list.factionID,
            prompt: theme,
            list: workspace.list
        )
        if Task.isCancelled { return nil }
        recordThemeBrief(brief: brief, steps: &steps, onStep: onStep)
        if workspace.list.detachmentIDs.isEmpty {
            onPhase?(.choosingDetachment)
            guard await pickDetachments(
                workspace: workspace,
                brief: brief,
                decider: decider,
                usedLaya: usedLaya,
                steps: &steps,
                onStep: onStep
            ) else { return nil }
        }
        onPhase?(.addingUnits)
        guard await addUnits(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        onPhase?(.attaching)
        guard await assignWarlord(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        guard await attachLeaders(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        onPhase?(.assigningEnhancements)
        guard await assignEnhancements(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        guard await packRemaining(
            workspace: workspace,
            brief: brief,
            decider: decider,
            usedLaya: usedLaya,
            steps: &steps,
            onStep: onStep
        ) else { return nil }
        if Task.isCancelled { return nil }
        return await finish(
            workspace: workspace,
            action: "Filled",
            brief: brief,
            usedLaya: usedLaya,
            decider: decider,
            steps: &steps,
            onStep: onStep
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
        let brief = ArmyListThemeBriefBuilder.heuristic(
            catalog: workspace.catalog,
            prompt: theme,
            list: workspace.list
        )
        onPhase?(.attaching)
        for _ in 0..<8 {
            if Task.isCancelled { return nil }
            let errors = workspace.validation.errors
            if errors.isEmpty { break }
            let repaired = await repair(
                error: errors[0],
                workspace: workspace,
                brief: brief,
                decider: decider,
                usedLaya: usedLaya,
                steps: &steps,
                onStep: onStep
            )
            if !repaired { break }
        }
        if Task.isCancelled { return nil }
        return await finish(
            workspace: workspace,
            action: "Repaired",
            brief: brief,
            usedLaya: usedLaya,
            decider: decider,
            steps: &steps,
            onStep: onStep
        )
    }

    // MARK: - Steps

    private static func pickDetachments(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        if Task.isCancelled { return false }
        guard let battle = workspace.catalog.battleSize(id: workspace.list.battleSizeID) else {
            return false
        }
        let candidates = ArmyListHarness.preferThemed(
            ArmyListPalette.legalDetachments(
                catalog: workspace.catalog,
                factionID: workspace.list.factionID,
                dpBudget: battle.detachmentPointsBudget,
                theme: brief.rankingText
            ),
            tokens: brief.tokens
        ) { detachment in
            ArmyListHarness.textMatchesTheme(
                "\(detachment.name) \(detachment.id) \(detachment.forceDisposition)",
                tokens: brief.tokens
            )
        }
        if candidates.isEmpty { return false }
        let shortlist = Array(candidates.prefix(ArmyListPalette.maxLayaOptions))
        let instructions = "Pick a detachment"
        guard let pick = await pickChoice(
            shortlist,
            instructions: instructions,
            option: { LayaChoiceOption($0.name, "\($0.detachmentPoints) DP") },
            decider: decider,
            usedLaya: usedLaya,
            workspace: workspace,
            brief: brief
        ) else { return false }
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: pick.item.id
        )
        record(
            title: "Detachment",
            instructions: instructions,
            decision: pick.decision,
            applied: "Detachment \(pick.item.name)",
            worker: pick.worker,
            steps: &steps,
            onStep: onStep
        )

        let spent = workspace.catalog.detachment(id: pick.item.id)?.detachmentPoints ?? pick.item.detachmentPoints
        let leftover = battle.detachmentPointsBudget - spent
        let extras = candidates.filter { $0.id != pick.item.id && $0.detachmentPoints <= leftover }
        if leftover > 0, !extras.isEmpty {
            if Task.isCancelled { return false }
            let extraList = Array(extras.prefix(ArmyListPalette.maxLayaOptions - 1))
            var extraPicks = [ExtraDetachmentPick(detachment: nil)]
            extraPicks.append(contentsOf: extraList.map { ExtraDetachmentPick(detachment: $0) })
            let extraInstructions = "Add a second detachment"
            guard let extraPick = await pickChoice(
                extraPicks,
                instructions: extraInstructions,
                option: { $0.option() },
                decider: decider,
                usedLaya: usedLaya,
                workspace: workspace,
                brief: brief
            ) else { return !Task.isCancelled }
            if let extra = extraPick.item.detachment {
                _ = ArmyListChatToolExecutor.setDetachments(
                    workspace: workspace,
                    detachmentIDsCSV: "\(pick.item.id),\(extra.id)"
                )
                record(
                    title: "Detachment",
                    instructions: extraInstructions,
                    decision: extraPick.decision,
                    applied: "Also \(extra.name)",
                    worker: extraPick.worker,
                    steps: &steps,
                    onStep: onStep
                )
            } else {
                record(
                    title: "Detachment",
                    instructions: extraInstructions,
                    decision: extraPick.decision,
                    applied: "One detachment",
                    worker: extraPick.worker,
                    steps: &steps,
                    onStep: onStep
                )
            }
        }
        return !Task.isCancelled
    }

    private static func addUnits(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        guard let battle = workspace.catalog.battleSize(id: workspace.list.battleSizeID) else {
            return false
        }
        var skippedSheetIDs: Set<String> = []
        var askedKeepAdding = false
        for _ in 0..<ArmyListPalette.maxAddSteps {
            if Task.isCancelled { return false }
            let remaining = battle.pointsLimit - workspace.validation.totalPoints
            let hasCharacter = ArmyListPalette.hasCharacter(list: workspace.list, catalog: workspace.catalog)
            if hasCharacter, remaining <= ArmyListPalette.goodEnoughSlack {
                return true
            }
            let cheapest = ArmyListPalette.cheapestLegalAdd(
                catalog: workspace.catalog,
                list: workspace.list,
                remainingPoints: remaining
            )
            if let cheapest, remaining < cheapest {
                return true
            }
            if usedLaya, !askedKeepAdding,
               ArmyListHarness.shouldAskToKeepAdding(
                hasCharacter: hasCharacter,
                remainingPoints: remaining,
                cheapestLegal: cheapest
               )
            {
                askedKeepAdding = true
                let keep = await askYesNo(
                    instructions: "Add another unit?",
                    falseText: "stop",
                    trueText: "keep adding",
                    title: "Add unit",
                    appliedYes: "Keep adding",
                    appliedNo: "Stopped adding",
                    decider: decider,
                    workspace: workspace,
                    brief: brief,
                    steps: &steps,
                    onStep: onStep
                )
                if !keep { return true }
            }
            var moves = legalAddShortlist(
                workspace: workspace,
                brief: brief,
                remainingPoints: remaining,
                hasCharacter: hasCharacter,
                charactersOnly: !hasCharacter,
                skippedSheetIDs: skippedSheetIDs
            )
            if moves.isEmpty, !hasCharacter {
                moves = legalAddShortlist(
                    workspace: workspace,
                    brief: brief,
                    remainingPoints: remaining,
                    hasCharacter: hasCharacter,
                    charactersOnly: false,
                    skippedSheetIDs: skippedSheetIDs
                )
            }
            if moves.isEmpty { return true }

            let instructions = hasCharacter ? "Add one unit" : "Add a Character"
            guard let pick = await pickChoice(
                moves,
                instructions: instructions,
                option: { $0.option() },
                decider: decider,
                usedLaya: usedLaya,
                workspace: workspace,
                brief: brief
            ) else { return true }
            let move = pick.item
            let requireCharacter = !hasCharacter
            let onTheme = await acceptThematicMove(
                name: move.sheet.name,
                sheet: move.sheet,
                requireCharacter: requireCharacter,
                remainingAlternatives: moves.count - 1,
                brief: brief,
                usedLaya: usedLaya,
                decider: decider,
                workspace: workspace,
                steps: &steps,
                onStep: onStep
            )
            if !onTheme {
                skippedSheetIDs.insert(move.sheet.id)
                continue
            }
            guard let models = await resolveModels(
                sheet: move.sheet,
                remainingPoints: remaining,
                usedLaya: usedLaya,
                decider: decider,
                workspace: workspace,
                brief: brief,
                steps: &steps,
                onStep: onStep
            ) else { return true }
            let output = ArmyListChatToolExecutor.addUnit(
                workspace: workspace,
                datasheetID: move.sheet.id,
                models: Double(models)
            )
            if output.hasPrefix("Rejected:") {
                record(
                    title: "Add unit",
                    instructions: instructions,
                    decision: pick.decision,
                    applied: "Skipped \(move.sheet.name)",
                    worker: pick.worker,
                    steps: &steps,
                    onStep: onStep
                )
                skippedSheetIDs.insert(move.sheet.id)
                continue
            }
            record(
                title: "Add unit",
                instructions: instructions,
                decision: pick.decision,
                applied: "Added \(move.sheet.name)×\(models)",
                worker: pick.worker,
                steps: &steps,
                onStep: onStep
            )
        }
        return !Task.isCancelled
    }

    private static func assignEnhancements(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        guard let battle = workspace.catalog.battleSize(id: workspace.list.battleSizeID) else {
            return false
        }
        var askedAssign = false
        for _ in 0..<battle.enhancementPickLimit {
            if Task.isCancelled { return false }
            let remainingPoints = battle.pointsLimit - workspace.validation.totalPoints
            let remainingPicks = battle.enhancementPickLimit - ArmyListPalette.enhancementPickSlots(
                list: workspace.list,
                catalog: workspace.catalog
            )
            let moves = ArmyListHarness.preferThemed(
                ArmyListPalette.legalEnhancements(
                    catalog: workspace.catalog,
                    list: workspace.list,
                    theme: brief.rankingText,
                    remainingPoints: remainingPoints,
                    remainingPicks: remainingPicks,
                    limit: ArmyListPalette.maxLayaOptions
                ),
                tokens: brief.tokens
            ) { move in
                ArmyListHarness.textMatchesTheme(
                    "\(move.enhancement.name) \(move.enhancement.id) \(move.unitName)",
                    tokens: brief.tokens
                )
            }
            if moves.isEmpty { return true }
            if usedLaya, !askedAssign {
                askedAssign = true
                let assign = await askYesNo(
                    instructions: "Assign an enhancement?",
                    falseText: "skip",
                    trueText: "assign",
                    title: "Enhancement",
                    appliedYes: "Assign enhancement",
                    appliedNo: "Skipped enhancements",
                    decider: decider,
                    workspace: workspace,
                    brief: brief,
                    steps: &steps,
                    onStep: onStep
                )
                if !assign { return true }
            }
            let instructions = "Pick an enhancement"
            guard let pick = await pickChoice(
                moves,
                instructions: instructions,
                option: { $0.option() },
                decider: decider,
                usedLaya: usedLaya,
                workspace: workspace,
                brief: brief
            ) else { return true }
            let move = pick.item
            let output = ArmyListChatToolExecutor.setEnhancement(
                workspace: workspace,
                unitID: move.unitID.uuidString,
                enhancementID: move.enhancement.id
            )
            if output.hasPrefix("Unknown") || output.hasPrefix("No unit") {
                record(
                    title: "Enhancement",
                    instructions: instructions,
                    decision: pick.decision,
                    applied: "Skipped \(move.enhancement.name)",
                    worker: pick.worker,
                    steps: &steps,
                    onStep: onStep
                )
                return true
            }
            record(
                title: "Enhancement",
                instructions: instructions,
                decision: pick.decision,
                applied: "\(move.enhancement.name) on \(move.unitName)",
                worker: pick.worker,
                steps: &steps,
                onStep: onStep
            )
        }
        return !Task.isCancelled
    }

    /// After the add loop stops, spend leftover points on themed legal units.
    /// One leftover candidate is mechanical. Several is a Laya choice.
    private static func packRemaining(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        guard let battle = workspace.catalog.battleSize(id: workspace.list.battleSizeID) else {
            return false
        }
        let remainingAtStart = battle.pointsLimit - workspace.validation.totalPoints
        if remainingAtStart <= ArmyListPalette.goodEnoughSlack { return true }
        if usedLaya {
            let spend = await askYesNo(
                instructions: "Spend leftover points?",
                falseText: "leave leftover",
                trueText: "pack",
                title: "Pack",
                appliedYes: "Pack leftover points",
                appliedNo: "Left leftover points",
                decider: decider,
                workspace: workspace,
                brief: brief,
                steps: &steps,
                onStep: onStep
            )
            if !spend { return true }
        }
        var skippedSheetIDs: Set<String> = []
        for _ in 0..<ArmyListPalette.maxAddSteps {
            if Task.isCancelled { return false }
            let remaining = battle.pointsLimit - workspace.validation.totalPoints
            if remaining <= ArmyListPalette.goodEnoughSlack { return true }
            if let cheapest = ArmyListPalette.cheapestLegalAdd(
                catalog: workspace.catalog,
                list: workspace.list,
                remainingPoints: remaining
            ), remaining < cheapest {
                return true
            }
            let hasCharacter = ArmyListPalette.hasCharacter(list: workspace.list, catalog: workspace.catalog)
            let moves = legalAddShortlist(
                workspace: workspace,
                brief: brief,
                remainingPoints: remaining,
                hasCharacter: hasCharacter,
                charactersOnly: false,
                skippedSheetIDs: skippedSheetIDs
            )
            guard !moves.isEmpty else { return true }
            let instructions = "Spend leftover points"
            guard let pick = await pickChoice(
                moves,
                instructions: instructions,
                option: { $0.option() },
                decider: decider,
                usedLaya: usedLaya,
                workspace: workspace,
                brief: brief
            ) else { return true }
            let move = pick.item
            let onTheme = await acceptThematicMove(
                name: move.sheet.name,
                sheet: move.sheet,
                requireCharacter: false,
                remainingAlternatives: moves.count - 1,
                brief: brief,
                usedLaya: usedLaya,
                decider: decider,
                workspace: workspace,
                steps: &steps,
                onStep: onStep
            )
            if !onTheme {
                skippedSheetIDs.insert(move.sheet.id)
                continue
            }
            guard let models = await resolveModels(
                sheet: move.sheet,
                remainingPoints: remaining,
                usedLaya: usedLaya,
                decider: decider,
                workspace: workspace,
                brief: brief,
                steps: &steps,
                onStep: onStep
            ) else { return true }
            let output = ArmyListChatToolExecutor.addUnit(
                workspace: workspace,
                datasheetID: move.sheet.id,
                models: Double(models)
            )
            if output.hasPrefix("Rejected:") { return true }
            record(
                title: "Pack",
                instructions: instructions,
                decision: pick.decision,
                applied: "Added \(move.sheet.name)×\(models)",
                worker: pick.worker,
                steps: &steps,
                onStep: onStep
            )
        }
        return !Task.isCancelled
    }

    private static func assignWarlord(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        if Task.isCancelled { return false }
        let characters = ArmyListHarness.preferThemed(
            ArmyListPalette.characters(on: workspace.list, catalog: workspace.catalog),
            tokens: brief.tokens
        ) { unit in
            guard let sheet = workspace.catalog.datasheet(id: unit.datasheetID) else { return false }
            return ArmyListPalette.matchesTheme(sheet: sheet, tokens: brief.tokens)
        }
        if characters.isEmpty { return true }
        let shortlist = Array(characters.prefix(ArmyListPalette.maxLayaOptions))
        let instructions = "Pick the Warlord"
        guard let pick = await pickChoice(
            shortlist,
            instructions: instructions,
            option: { unit in
                let name = workspace.catalog.datasheet(id: unit.datasheetID)?.name ?? unit.datasheetID
                return LayaChoiceOption(name)
            },
            decider: decider,
            usedLaya: usedLaya,
            workspace: workspace,
            brief: brief
        ) else { return true }
        if workspace.list.warlordUnitID != pick.item.id {
            _ = ArmyListChatToolExecutor.setWarlord(workspace: workspace, unitID: pick.item.id.uuidString)
        }
        let name = workspace.catalog.datasheet(id: pick.item.datasheetID)?.name ?? pick.item.datasheetID
        record(
            title: "Warlord",
            instructions: instructions,
            decision: pick.decision,
            applied: "Warlord \(name)",
            worker: pick.worker,
            steps: &steps,
            onStep: onStep
        )
        return true
    }

    private static func attachLeaders(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
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
            let bodies = ArmyListHarness.preferThemed(
                ArmyListPalette.legalBodyguards(
                    catalog: workspace.catalog,
                    list: workspace.list,
                    characterSheet: sheet
                ),
                tokens: brief.tokens
            ) { body in
                guard let bodySheet = workspace.catalog.datasheet(id: body.datasheetID) else { return false }
                return ArmyListPalette.matchesTheme(sheet: bodySheet, tokens: brief.tokens)
            }
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
                        worker: .mechanical,
                        steps: &steps,
                        onStep: onStep
                    )
                }
                continue
            }
            let noneSlots = sheet.mustAttach ? 0 : 1
            let bodySlice = Array(bodies.prefix(ArmyListPalette.maxLayaOptions - noneSlots))
            var targets = bodySlice.map { body in
                let name = workspace.catalog.datasheet(id: body.datasheetID)?.name ?? body.datasheetID
                return AttachTarget(unit: body, label: name)
            }
            if !sheet.mustAttach {
                targets.append(AttachTarget(unit: nil, label: "none"))
            }
            let instructions = "Attach \(sheet.name)"
            guard let pick = await pickChoice(
                targets,
                instructions: instructions,
                option: { target in
                    if target.unit == nil {
                        return LayaChoiceOption("none", "leave unattached")
                    }
                    return LayaChoiceOption(target.label)
                },
                decider: decider,
                usedLaya: usedLaya,
                workspace: workspace,
                brief: brief
            ) else { continue }
            guard let body = pick.item.unit else {
                record(
                    title: "Attach",
                    instructions: instructions,
                    decision: pick.decision,
                    applied: "Left \(sheet.name) unattached",
                    worker: pick.worker,
                    steps: &steps,
                    onStep: onStep
                )
                continue
            }
            _ = ArmyListChatToolExecutor.attachCharacter(
                workspace: workspace,
                characterUnitID: character.id.uuidString,
                bodyUnitID: body.id.uuidString
            )
            let bodyName = workspace.catalog.datasheet(id: body.datasheetID)?.name ?? body.datasheetID
            record(
                title: "Attach",
                instructions: instructions,
                decision: pick.decision,
                applied: "Attached \(sheet.name) to \(bodyName)",
                worker: pick.worker,
                steps: &steps,
                onStep: onStep
            )
        }
        return !Task.isCancelled
    }

    private static func repair(
        error: ValidationIssue,
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        switch error.code {
        case "warlord.missing":
            return await assignWarlord(
                workspace: workspace,
                brief: brief,
                decider: decider,
                usedLaya: usedLaya,
                steps: &steps,
                onStep: onStep
            )
        case "detachment.required":
            return await pickDetachments(
                workspace: workspace,
                brief: brief,
                decider: decider,
                usedLaya: usedLaya,
                steps: &steps,
                onStep: onStep
            )
        case "unit.mustAttach":
            return await attachLeaders(
                workspace: workspace,
                brief: brief,
                decider: decider,
                usedLaya: usedLaya,
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
                    worker: .mechanical,
                    steps: &steps,
                    onStep: onStep
                )
            }
            return true
        case "points.overLimit":
            return await cutForPoints(
                workspace: workspace,
                brief: brief,
                decider: decider,
                usedLaya: usedLaya,
                steps: &steps,
                onStep: onStep
            )
        case "unit.duplicateCap", "unit.epicHeroDuplicate":
            return removeExtraCopy(workspace: workspace, steps: &steps, onStep: onStep)
        case "dp.overBudget":
            return await dropDetachmentForBudget(
                workspace: workspace,
                brief: brief,
                decider: decider,
                usedLaya: usedLaya,
                steps: &steps,
                onStep: onStep
            )
        case "list.empty":
            return await addUnits(
                workspace: workspace,
                brief: brief,
                decider: decider,
                usedLaya: usedLaya,
                steps: &steps,
                onStep: onStep
            )
        case "enhancement.pickLimit", "enhancement.onePerUnit", "enhancement.unknown",
             "enhancement.detachmentNotSelected", "enhancement.upgradeOnCharacter",
             "enhancement.upgradeCap", "enhancement.requiresCharacter":
            return clearOneEnhancement(
                error: error,
                workspace: workspace,
                steps: &steps,
                onStep: onStep
            )
        default:
            return false
        }
    }

    private static func cutForPoints(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        let slice = ArmyListHarness.cutCandidates(
            list: workspace.list,
            catalog: workspace.catalog,
            tokens: brief.tokens,
            limit: ArmyListPalette.maxLayaOptions
        )
        if slice.isEmpty { return false }
        let instructions = "Drop a unit"
        guard let pick = await pickChoice(
            slice,
            instructions: instructions,
            option: { unit in
                let name = workspace.catalog.datasheet(id: unit.datasheetID)?.name ?? unit.datasheetID
                return LayaChoiceOption(name)
            },
            decider: decider,
            usedLaya: usedLaya,
            workspace: workspace,
            brief: brief
        ) else { return false }
        let name = workspace.catalog.datasheet(id: pick.item.datasheetID)?.name ?? pick.item.datasheetID
        _ = ArmyListChatToolExecutor.removeUnit(workspace: workspace, unitID: pick.item.id.uuidString)
        record(
            title: "Cut",
            instructions: instructions,
            decision: pick.decision,
            applied: "Removed \(name)",
            worker: pick.worker,
            steps: &steps,
            onStep: onStep
        )
        return true
    }

    private static func clearOneEnhancement(
        error: ValidationIssue,
        workspace: ArmyListChatWorkspace,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) -> Bool {
        let target = error.unitID.flatMap { id in
            workspace.list.units.first { $0.id == id && !$0.enhancementIDs.isEmpty }
        } ?? workspace.list.units.first { !$0.enhancementIDs.isEmpty }
        guard let target else { return false }
        _ = ArmyListChatToolExecutor.setEnhancement(
            workspace: workspace,
            unitID: target.id.uuidString,
            enhancementID: "none"
        )
        let name = workspace.catalog.datasheet(id: target.datasheetID)?.name ?? target.datasheetID
        let decision = LayaGreedyDecider.choice(
            label: "none",
            options: [LayaChoiceOption("none")],
            act: 1
        )
        record(
            title: "Enhancement",
            instructions: "Clear illegal enhancement",
            decision: decision,
            applied: "Cleared enhancement on \(name)",
            worker: .mechanical,
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
        let warlord = workspace.list.warlordUnitID
        let pool = over.value.filter { $0.id != warlord }
        let victim = (pool.isEmpty ? over.value : pool).last
        guard let victim else { return false }
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
            worker: .mechanical,
            steps: &local,
            onStep: onStep
        )
        steps = local
        return true
    }

    private static func dropDetachmentForBudget(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        decider: any LayaDeciding,
        usedLaya: Bool,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        let ids = workspace.list.detachmentIDs
        guard ids.count > 1 else { return false }
        let options: [DetachmentDropPick] = ids.compactMap { id in
            guard let detachment = workspace.catalog.detachment(id: id) else { return nil }
            return DetachmentDropPick(id: id, name: detachment.name)
        }
        guard options.count > 1 else { return false }
        let instructions = "Drop a detachment"
        let pick: ChoicePick<DetachmentDropPick>
        if usedLaya {
            guard let chosen = await pickChoice(
                options,
                instructions: instructions,
                option: { LayaChoiceOption($0.name) },
                decider: decider,
                usedLaya: true,
                workspace: workspace,
                brief: brief
            ) else { return false }
            pick = chosen
        } else {
            guard let dropped = options.last else { return false }
            pick = ChoicePick(
                item: dropped,
                decision: ArmyListHarness.stampedChoice(label: dropped.name),
                worker: .mechanical
            )
        }
        let kept = ids.filter { $0 != pick.item.id }
        guard !kept.isEmpty else { return false }
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: kept.joined(separator: ",")
        )
        record(
            title: "Detachment",
            instructions: instructions,
            decision: pick.decision,
            applied: "Dropped \(pick.item.name)",
            worker: pick.worker,
            steps: &steps,
            onStep: onStep
        )
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
        worker: ArmyListHarness.Worker,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) {
        let step = ArmyListDecisionStep(
            title: title,
            instructions: instructions,
            decision: decision,
            applied: applied,
            worker: worker
        )
        steps.append(step)
        onStep?(step)
    }

    private struct ChoicePick<T> {
        let item: T
        let decision: LayaDecision
        let worker: ArmyListHarness.Worker
    }

    private struct ExtraDetachmentPick {
        let detachment: DetachmentDefinition?
        func option() -> LayaChoiceOption {
            if let detachment {
                return LayaChoiceOption(detachment.name, "\(detachment.detachmentPoints) DP")
            }
            return LayaChoiceOption("none", "keep one detachment")
        }
    }

    private struct AttachTarget {
        let unit: ListUnitInstance?
        let label: String
    }

    private struct DetachmentDropPick {
        let id: String
        let name: String
    }

    /// One legal option is catalog work. Two or more asks the decider; the
    /// worker tag is Laya only when the graph is loaded.
    private static func pickChoice<T>(
        _ items: [T],
        instructions: String,
        option: (T) -> LayaChoiceOption,
        decider: any LayaDeciding,
        usedLaya: Bool,
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief
    ) async -> ChoicePick<T>? {
        if items.isEmpty { return nil }
        if items.count == 1 {
            let item = items[0]
            let opt = option(item)
            return ChoicePick(
                item: item,
                decision: ArmyListHarness.stampedChoice(label: opt.label, options: [opt]),
                worker: .mechanical
            )
        }
        let options = items.map(option)
        let decision = await decide(
            decider: decider,
            state: snapshot(workspace: workspace, brief: brief),
            question: .choice(instructions: instructions, options: options)
        )
        let item = items.first { option($0).label == decision.choiceLabel } ?? items[0]
        return ChoicePick(
            item: item,
            decision: decision,
            worker: ArmyListHarness.choiceWorker(optionCount: items.count, usedLaya: usedLaya)
        )
    }

    /// Two or more legal sizes is a Laya pick. One size is catalog work.
    private static func resolveModels(
        sheet: DatasheetDefinition,
        remainingPoints: Int,
        usedLaya: Bool,
        decider: any LayaDeciding,
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Int? {
        let sizes = ArmyListPalette.legalModelCounts(
            sheet: sheet,
            list: workspace.list,
            remainingPoints: remainingPoints
        )
        if sizes.isEmpty { return nil }
        guard let pick = await pickChoice(
            sizes,
            instructions: "How many \(sheet.name)?",
            option: { $0.option() },
            decider: decider,
            usedLaya: usedLaya,
            workspace: workspace,
            brief: brief
        ) else { return nil }
        if sizes.count >= 2 {
            record(
                title: "Models",
                instructions: "How many \(sheet.name)?",
                decision: pick.decision,
                applied: "\(sheet.name)×\(pick.item.models)",
                worker: pick.worker,
                steps: &steps,
                onStep: onStep
            )
        }
        return pick.item.models
    }

    private static func askYesNo(
        instructions: String,
        falseText: String,
        trueText: String,
        title: String,
        appliedYes: String,
        appliedNo: String,
        decider: any LayaDeciding,
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        let decision = await decide(
            decider: decider,
            state: snapshot(workspace: workspace, brief: brief),
            question: .noul(
                instructions: instructions,
                falseText: falseText,
                trueText: trueText
            )
        )
        let yes = decision.noulHolds ?? true
        record(
            title: title,
            instructions: instructions,
            decision: decision,
            applied: yes ? appliedYes : appliedNo,
            worker: .laya,
            steps: &steps,
            onStep: onStep
        )
        return yes
    }

    private static func recordThemeBrief(
        brief: ArmyListThemeBrief,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) {
        let line = brief.snapshotTheme
        if line.isEmpty { return }
        let worker: ArmyListHarness.Worker =
            brief.source == .foundationModels ? .foundationModels : .mechanical
        record(
            title: "Theme",
            instructions: "Theme brief",
            decision: ArmyListHarness.stampedChoice(label: line),
            applied: "Theme: \(line)",
            worker: worker,
            steps: &steps,
            onStep: onStep
        )
    }

    private static func scoreTheme(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        usedLaya: Bool,
        decider: any LayaDeciding,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> String? {
        if !usedLaya { return nil }
        if brief.snapshotTheme.isEmpty, brief.tokens.isEmpty { return nil }
        if workspace.list.units.isEmpty { return nil }
        let instructions = "How on-theme is this list?"
        let decision = await decide(
            decider: decider,
            state: snapshot(workspace: workspace, brief: brief),
            question: .score(
                instructions: instructions,
                levels: ArmyListHarness.themeScoreLevels
            )
        )
        let label = ArmyListHarness.scoreLegendLabel(decision)
        record(
            title: "Theme score",
            instructions: instructions,
            decision: decision,
            applied: "Theme score: \(label)",
            worker: .laya,
            steps: &steps,
            onStep: onStep
        )
        return label
    }

    private static func finish(
        workspace: ArmyListChatWorkspace,
        action: String,
        brief: ArmyListThemeBrief,
        usedLaya: Bool,
        decider: any LayaDeciding,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> ArmyListConstructionResult? {
        if Task.isCancelled { return nil }
        let scoreLabel = await scoreTheme(
            workspace: workspace,
            brief: brief,
            usedLaya: usedLaya,
            decider: decider,
            steps: &steps,
            onStep: onStep
        )
        return ArmyListConstructionResult(
            list: workspace.list,
            steps: steps,
            usedLaya: usedLaya,
            summary: summary(
                workspace: workspace,
                action: action,
                brief: brief,
                themeScoreLabel: scoreLabel
            ),
            themeBrief: brief,
            themeScoreLabel: scoreLabel
        )
    }

    static func listName(
        catalog: ArmyCatalog,
        factionID: String,
        battleSizeID: String,
        theme: String,
        userName: String?,
        brief: ArmyListThemeBrief? = nil
    ) -> String {
        if let userName {
            let trimmed = userName.trimmingCharacters(in: .whitespacesAndNewlines)
            if !trimmed.isEmpty { return trimmed }
        }
        if let brief {
            let named = ArmyListThemeBriefBuilder.clipListName(brief.listName)
            if !named.isEmpty { return named }
            if brief.source == .foundationModels {
                let fromSummary = ArmyListThemeBriefBuilder.clipListName(brief.summary)
                if !fromSummary.isEmpty { return fromSummary }
            }
        }
        let faction = catalog.faction(id: factionID)?.name ?? factionID
        let themeBit = theme.trimmingCharacters(in: .whitespacesAndNewlines)
        if !themeBit.isEmpty {
            return "\(faction) \(themeBit)"
        }
        let battle = catalog.battleSize(id: battleSizeID)?.name ?? battleSizeID
        return "\(faction) \(battle)"
    }

    private static func summary(
        workspace: ArmyListChatWorkspace,
        action: String,
        brief: ArmyListThemeBrief,
        themeScoreLabel: String?
    ) -> String {
        let result = workspace.validation
        let limit = workspace.catalog.battleSize(id: workspace.list.battleSizeID)?.pointsLimit ?? 0
        let legal = result.isLegal ? "Legal" : "Illegal"
        var text =
            "\(action) \(workspace.list.name): \(result.totalPoints)/\(limit) pts, \(legal), \(workspace.list.units.count) units."
        let themeBit = brief.snapshotTheme
        if !themeBit.isEmpty {
            text += " Theme: \(themeBit)."
        }
        if let themeScoreLabel {
            text += " Theme score: \(themeScoreLabel)."
        }
        return text
    }

    private static func snapshot(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief
    ) -> String {
        ArmyListLayaSnapshot.text(
            list: workspace.list,
            catalog: workspace.catalog,
            theme: brief.snapshotTheme,
            validation: workspace.validation
        )
    }

    private static func legalAddShortlist(
        workspace: ArmyListChatWorkspace,
        brief: ArmyListThemeBrief,
        remainingPoints: Int,
        hasCharacter: Bool,
        charactersOnly: Bool,
        skippedSheetIDs: Set<String>
    ) -> [ArmyListPalette.AddMove] {
        let pool = ArmyListPalette.legalAdds(
            catalog: workspace.catalog,
            list: workspace.list,
            theme: brief.rankingText,
            remainingPoints: remainingPoints,
            hasCharacter: hasCharacter,
            charactersOnly: charactersOnly,
            limit: ArmyListPalette.maxLayaOptions + skippedSheetIDs.count
        )
        let filtered = pool.filter { !skippedSheetIDs.contains($0.sheet.id) }
        let themed = ArmyListHarness.preferThemed(filtered, tokens: brief.tokens) { move in
            ArmyListPalette.matchesTheme(sheet: move.sheet, tokens: brief.tokens)
        }
        return Array(themed.prefix(ArmyListPalette.maxLayaOptions))
    }

    /// Token overlap is mechanical. Laya yes/no only when the datasheet misses
    /// every brief token and Laya is loaded.
    private static func acceptThematicMove(
        name: String,
        sheet: DatasheetDefinition,
        requireCharacter: Bool,
        remainingAlternatives: Int,
        brief: ArmyListThemeBrief,
        usedLaya: Bool,
        decider: any LayaDeciding,
        workspace: ArmyListChatWorkspace,
        steps: inout [ArmyListDecisionStep],
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)?
    ) async -> Bool {
        switch ArmyListHarness.themeRoute(
            sheet: sheet,
            tokens: brief.tokens,
            usedLaya: usedLaya,
            requireCharacter: requireCharacter,
            remainingAlternatives: remainingAlternatives
        ) {
        case .accept:
            return true
        case .reject:
            record(
                title: "On theme",
                instructions: "Does \(name) fit the theme?",
                decision: LayaGreedyDecider.noul(probability: 0.1),
                applied: "Off-theme: \(name)",
                worker: .mechanical,
                steps: &steps,
                onStep: onStep
            )
            return false
        case .askLaya:
            let instructions = "Does \(name) fit the theme?"
            let decision = await decide(
                decider: decider,
                state: snapshot(workspace: workspace, brief: brief),
                question: .noul(
                    instructions: instructions,
                    falseText: "off-theme",
                    trueText: "on-theme"
                )
            )
            var accepted = decision.noulHolds ?? true
            if !accepted, requireCharacter, remainingAlternatives == 0 {
                accepted = true
            }
            record(
                title: "On theme",
                instructions: instructions,
                decision: accepted == (decision.noulHolds ?? true)
                    ? decision
                    : LayaGreedyDecider.noul(probability: accepted ? 0.9 : 0.1),
                applied: accepted ? "On-theme: \(name)" : "Off-theme: \(name)",
                worker: .laya,
                steps: &steps,
                onStep: onStep
            )
            return accepted
        }
    }
}
