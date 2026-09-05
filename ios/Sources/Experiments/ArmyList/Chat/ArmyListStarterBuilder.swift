import Foundation

/// Composes a self-contained prompt for a from-scratch build and runs it.
///
/// The on-device model has a 4096-token window (see the
/// `foundation-models-context` skill). The interactive chat lets the model
/// discover ids with `searchCatalog`, but a one-shot "Build starter list" that
/// chains `getListSummary` → `searchCatalog` → `applyRosterPlan` across a dozen
/// resident tool schemas is unreliable: the model runs out of room or invents
/// ids that never resolve, so the roster comes back empty. Instead we hand the
/// model everything it needs up front — the points limit, DP budget, valid
/// detachment ids, and a theme-ranked shortlist of unit ids with points — and
/// let it make a single `applyRosterPlan` call against a builder-mode runtime
/// that registers only that one tool.
enum ArmyListStarterPrompt {
    /// Words too generic to steer unit selection.
    private static let stopWords: Set<String> = [
        "the", "and", "with", "for", "list", "army", "only", "all",
        "some", "few", "lots", "many", "themed", "theme", "build",
        "make", "create", "using", "use", "from", "that", "this",
    ]

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
            lines.append("Theme: \(trimmedTheme). Favor units that fit it and name the list accordingly.")
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
            for candidate in candidateUnits(
                catalog: catalog,
                factionID: factionID,
                battleSize: battle,
                theme: trimmedTheme,
                limit: maxUnits
            ) {
                lines.append(candidate.line)
            }
        }

        lines.append("")
        lines.append(
            "Call applyRosterPlan exactly once: pick one detachment id above within the DP budget, "
            + "and units from the ids above. Get as close to \(pointsLimit) pts as you can — "
            + "keep adding units until no listed unit fits the points that remain. "
            + "Use pts@models sizes and max copy counts from the table; repeat an id to field another copy. "
            + "Include at least one Character for the Warlord."
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

    private struct Candidate {
        let sheet: DatasheetDefinition
        let battleSize: BattleSizeDefinition
        let score: Int

        var line: String {
            var flags: [String] = []
            if sheet.characterRole != nil { flags.append("Character") }
            if sheet.battleline { flags.append("Battleline") }
            if sheet.dedicatedTransport { flags.append("Transport") }
            let role = flags.isEmpty ? "-" : flags.joined(separator: ",")
            let options = Self.pointsOptions(sheet: sheet)
            let maxCopies = Self.duplicateLimit(for: sheet, battleSize: battleSize)
            return "\(sheet.id) | \(sheet.name) | \(options) | \(role) | \(maxCopies)"
        }

        private static func pointsOptions(sheet: DatasheetDefinition) -> String {
            sheet.modelCounts.compactMap { models in
                guard let pts = sheet.points(models: models, copyIndex: 1) else { return nil }
                return "\(pts)@\(models)"
            }.joined(separator: ",")
        }

        private static func duplicateLimit(
            for sheet: DatasheetDefinition,
            battleSize: BattleSizeDefinition
        ) -> Int {
            let sizeLimit: Int
            if sheet.battleline {
                sizeLimit = battleSize.battlelineDuplicateLimit
            } else if sheet.dedicatedTransport {
                sizeLimit = battleSize.dedicatedTransportDuplicateLimit
            } else {
                sizeLimit = battleSize.datasheetDuplicateLimit
            }
            if let override = sheet.maxCopiesOverride {
                return min(override, sizeLimit)
            }
            return sizeLimit
        }
    }

    /// Theme-ranked shortlist. Theme matches float to the top; characters and
    /// battleline get a small nudge. Guarantees at least one Character survives
    /// the cut.
    private static func candidateUnits(
        catalog: ArmyCatalog,
        factionID: String,
        battleSize: BattleSizeDefinition,
        theme: String,
        limit: Int
    ) -> [Candidate] {
        let tokens = themeTokens(theme)
        let eligible: [Candidate] = catalog.datasheets.compactMap { sheet in
            guard sheet.factionID == factionID, !sheet.legends else { return nil }
            guard sheet.points(models: sheet.modelCounts.first ?? sheet.minModels, copyIndex: 1) != nil else {
                return nil
            }
            var score = 0
            if !tokens.isEmpty {
                let haystack = ([sheet.name, sheet.id] + sheet.keywords)
                    .joined(separator: " ")
                    .lowercased()
                score += tokens.filter { haystack.contains($0) }.count * 100
            }
            if sheet.characterRole != nil { score += 10 }
            if sheet.battleline { score += 5 }
            return Candidate(sheet: sheet, battleSize: battleSize, score: score)
        }

        let ranked = eligible.sorted { lhs, rhs in
            if lhs.score != rhs.score { return lhs.score > rhs.score }
            return lhs.sheet.name.localizedCaseInsensitiveCompare(rhs.sheet.name) == .orderedAscending
        }

        var chosen = Array(ranked.prefix(limit))
        // A Warlord needs a Character; make sure the palette contains one even
        // when a narrow theme crowds them out.
        if !chosen.contains(where: { $0.sheet.characterRole != nil }),
           let character = ranked.first(where: { $0.sheet.characterRole != nil }) {
            if !chosen.isEmpty { chosen.removeLast() }
            chosen.append(character)
        }
        return chosen
    }

    private static func themeTokens(_ theme: String) -> [String] {
        theme
            .lowercased()
            .components(separatedBy: CharacterSet.alphanumerics.inverted)
            .map { $0.trimmingCharacters(in: .whitespaces) }
            .filter { $0.count >= 3 && !stopWords.contains($0) }
    }
}

/// Runs the starter build on the on-device model, retrying a few times because
/// generation is stochastic. Returns the first non-empty roster, preferring a
/// legal one; returns `nil` only when the model is unavailable or every attempt
/// came back empty.
@MainActor
enum ArmyListStarterBuilder {
    static func build(
        catalog: ArmyCatalog,
        factionID: String,
        battleSizeID: String,
        theme: String,
        userName: String?,
        attempts: Int = 3
    ) async -> ArmyListDocument? {
        let prompt = ArmyListStarterPrompt.prompt(
            catalog: catalog,
            factionID: factionID,
            battleSizeID: battleSizeID,
            theme: theme
        )
        var fallback: ArmyListDocument?
        for _ in 0..<max(1, attempts) {
            let blank = ArmyListDocument(
                name: userName ?? "New list",
                catalogVersion: catalog.version,
                factionID: factionID,
                battleSizeID: battleSizeID
            )
            let workspace = ArmyListChatWorkspace(list: blank, catalog: catalog)
            let runtime = ArmyListChatRuntime(workspace: workspace, mode: .builder)
            guard runtime.isModelAvailable else { return nil }
            await runtime.send(prompt: prompt, displayText: "Build starter list")
            guard !workspace.list.units.isEmpty else { continue }
            var built = workspace.list
            if let userName, !userName.isEmpty {
                built.name = userName
            }
            if workspace.validation.isLegal {
                return built
            }
            if fallback == nil {
                fallback = built
            }
        }
        if let userName, !userName.isEmpty {
            fallback?.name = userName
        }
        return fallback
    }
}
