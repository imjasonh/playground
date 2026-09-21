import Foundation

/// AFM-era starter prompt. Construction no longer sends this to Foundation
/// Models; tests still check that the shortlist ranks theme matches first.
enum ArmyListStarterPrompt {
    /// Builds the prompt. `maxUnits` caps the candidate list so the prompt stays
    /// well within the context window even for large factions.
    static func prompt(
        catalog: ArmyCatalog,
        factionID: String,
        battleSizeID: String,
        theme: String,
        maxUnits: Int = 22
    ) -> String {
        let factionName = catalog.faction(id: factionID)?.name ?? factionID
        let battle = catalog.battleSize(id: battleSizeID)
        let pointsLimit = battle?.pointsLimit ?? 0
        let dpBudget = battle?.detachmentPointsBudget ?? 0
        let battleName = battle?.name ?? battleSizeID
        let trimmedTheme = theme.trimmingCharacters(in: .whitespacesAndNewlines)

        var lines: [String] = []
        lines.append("Build one \(factionName) army list for \(battleName) (\(pointsLimit) pts, \(dpBudget) DP budget).")
        if !trimmedTheme.isEmpty {
            lines.append(
                "Theme: \(trimmedTheme). Prefer themed units and name the list accordingly — still spend as close to \(pointsLimit) pts as you can."
            )
        }

        let detachments = catalog.detachments
            .filter { $0.factionID == factionID && $0.detachmentPoints <= dpBudget }
            .sorted { $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending }
        if detachments.isEmpty {
            lines.append("")
            lines.append("No detachments fit the \(dpBudget) DP budget for this battle size.")
        } else {
            lines.append("")
            lines.append("Detachments (id | name | DP):")
            for detachment in detachments.prefix(12) {
                lines.append("\(detachment.id) | \(detachment.name) | \(detachment.detachmentPoints) DP")
            }
        }

        lines.append("")
        lines.append("Units (id | name | pts@models | role | max):")
        if let battle {
            for sheet in ArmyListPalette.promptSheets(
                catalog: catalog,
                factionID: factionID,
                battleSize: battle,
                theme: trimmedTheme,
                limit: maxUnits
            ) {
                lines.append(ArmyListPalette.promptLine(sheet: sheet, battleSize: battle))
            }
        }

        lines.append("")
        lines.append(
            "Call applyRosterPlan exactly once: pick one detachment id above within the DP budget, "
            + "and units from the ids above. Get as close to \(pointsLimit) pts as you can "
            + "(aim to leave at most ~25 pts unused) — keep adding until no listed unit fits the points that remain. "
            + "Use pts@models sizes and max copy counts from the table; repeat an id to field another copy. "
            + "Include at least one Character for the Warlord."
            + (trimmedTheme.isEmpty ? "" : " Prefer themed units from the list above.")
        )
        return lines.joined(separator: "\n")
    }

    /// When non-nil, starter build cannot succeed at this battle size (no model call).
    static func buildFeasibilityIssue(
        catalog: ArmyCatalog,
        factionID: String,
        battleSizeID: String
    ) -> String? {
        guard let battle = catalog.battleSize(id: battleSizeID) else { return nil }
        let detachments = catalog.detachments.filter {
            $0.factionID == factionID && $0.detachmentPoints <= battle.detachmentPointsBudget
        }
        if detachments.isEmpty {
            return "No detachments fit the \(battle.detachmentPointsBudget) DP budget for \(battle.name). Choose a larger battle size or create a blank list."
        }
        var cheapest: Int?
        var hasCharacter = false
        for sheet in catalog.datasheets where sheet.factionID == factionID && !sheet.legends {
            if sheet.characterRole != nil { hasCharacter = true }
            for models in sheet.modelCounts {
                if let pts = sheet.points(models: models, copyIndex: 1) {
                    cheapest = min(cheapest ?? pts, pts)
                }
            }
        }
        if let cheapest, cheapest > battle.pointsLimit {
            return "The cheapest unit is \(cheapest) pts; \(battle.name) allows \(battle.pointsLimit). Choose a larger battle size or create a blank list."
        }
        if !hasCharacter {
            return "This faction has no Character datasheets, so a Warlord cannot be set. Create a blank list to edit manually."
        }
        return nil
    }
}

/// Milestones for the New list sheet while a starter build runs.
struct ArmyListStarterBuildProgress: Equatable {
    enum Phase: Equatable {
        case loadingModel
        case preparing
        case choosingDetachment
        case addingUnits
        case attaching
        case assigningEnhancements
        case finishing
    }

    let phase: Phase

    /// Determinate fraction for `ProgressView(value:total:)`.
    var fractionComplete: Double {
        switch phase {
        case .loadingModel: return 0.02
        case .preparing: return 0.05
        case .choosingDetachment: return 0.18
        case .addingUnits: return 0.48
        case .attaching: return 0.70
        case .assigningEnhancements: return 0.86
        case .finishing: return 1.0
        }
    }

    /// Eases a displayed bar value toward the next milestone so a long Laya
    /// pass still looks like it is filling. The finishing phase snaps to full.
    static func trickle(
        from current: Double,
        milestone: ArmyListStarterBuildProgress?
    ) -> Double {
        guard let milestone else {
            return min(0.9, current + (0.9 - current) * 0.05)
        }
        let floor = milestone.fractionComplete
        if milestone.phase == .finishing {
            return 1.0
        }
        let ceiling = min(0.95, floor + 0.22)
        let eased = current + (ceiling - current) * 0.06
        return min(ceiling, max(floor, eased))
    }

    var statusText: String {
        switch phase {
        case .loadingModel:
            return "Loading Laya…"
        case .preparing:
            return "Preparing roster options…"
        case .choosingDetachment:
            return "Choosing a detachment…"
        case .addingUnits:
            return "Adding units…"
        case .attaching:
            return "Attaching leaders…"
        case .assigningEnhancements:
            return "Choosing enhancements…"
        case .finishing:
            return "Opening list…"
        }
    }
}

/// Builds a starter list with Laya when the shared graph is loaded, otherwise
/// with the greedy first-option decider. Apple Intelligence can write a short
/// theme brief and a list name first. Construction still runs when that model
/// is off.
@MainActor
enum ArmyListStarterBuilder {
    static func build(
        catalog: ArmyCatalog,
        factionID: String,
        battleSizeID: String,
        theme: String,
        userName: String?,
        decider: (any LayaDeciding)? = nil,
        store: LayaModelStore? = nil,
        onProgress: (@MainActor (ArmyListStarterBuildProgress) -> Void)? = nil,
        onStep: (@MainActor (ArmyListDecisionStep) -> Void)? = nil
    ) async -> ArmyListDocument? {
        if Task.isCancelled { return nil }
        let store = store ?? LayaModelStore.shared
        if store.isDownloaded, !store.isReady {
            onProgress?(ArmyListStarterBuildProgress(phase: .loadingModel))
            await store.prepare()
        } else {
            onProgress?(ArmyListStarterBuildProgress(phase: .preparing))
        }
        if Task.isCancelled { return nil }
        let engine = decider ?? ArmyListDecisionController.activeDecider(store: store)
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: factionID,
            battleSizeID: battleSizeID,
            theme: theme,
            userName: userName,
            decider: engine,
            usedLaya: store.isReady,
            onPhase: { phase in
                onProgress?(ArmyListStarterBuildProgress(phase: phase))
            },
            onStep: onStep
        )
        if Task.isCancelled { return nil }
        guard let result, !result.list.units.isEmpty else { return nil }
        onProgress?(ArmyListStarterBuildProgress(phase: .finishing))
        return result.list
    }
}
