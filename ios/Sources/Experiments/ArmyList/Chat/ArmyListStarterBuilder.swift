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
            .filter { $0.factionID == factionID }
            .sorted { $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending }
        if !detachments.isEmpty {
            lines.append("")
            lines.append("Detachments (id | name | DP):")
            for detachment in detachments.prefix(12) {
                lines.append("\(detachment.id) | \(detachment.name) | \(detachment.detachmentPoints) DP")
            }
        }

        lines.append("")
        lines.append("Units (id | name | points | role):")
        for candidate in candidateUnits(catalog: catalog, factionID: factionID, theme: trimmedTheme, limit: maxUnits) {
            lines.append(candidate.line)
        }

        lines.append("")
        lines.append(
            "Call applyRosterPlan exactly once: pick one detachment id above within the DP budget, "
            + "and units from the ids above totaling as close to \(pointsLimit) pts as you can without going over. "
            + "Repeat a unit id (e.g. leman-russ-battle-tank:1,leman-russ-battle-tank:1) to field more than one. "
            + "Include at least one Character for the Warlord."
        )
        return lines.joined(separator: "\n")
    }

    private struct Candidate {
        let sheet: DatasheetDefinition
        let models: Int
        let points: Int
        let score: Int

        var line: String {
            var flags: [String] = []
            if sheet.characterRole != nil { flags.append("Character") }
            if sheet.battleline { flags.append("Battleline") }
            if sheet.dedicatedTransport { flags.append("Transport") }
            let role = flags.isEmpty ? "-" : flags.joined(separator: ",")
            return "\(sheet.id) | \(sheet.name) | \(points)pts@\(models) | \(role)"
        }
    }

    /// Theme-ranked, points-priced shortlist. Theme matches float to the top;
    /// characters and battleline get a small nudge so every palette can build a
    /// legal list even when the theme is narrow. Guarantees at least one
    /// Character survives the cut.
    private static func candidateUnits(
        catalog: ArmyCatalog,
        factionID: String,
        theme: String,
        limit: Int
    ) -> [Candidate] {
        let tokens = themeTokens(theme)
        let eligible: [Candidate] = catalog.datasheets.compactMap { sheet in
            guard sheet.factionID == factionID, !sheet.legends else { return nil }
            let models = sheet.modelCounts.first ?? sheet.minModels
            guard let points = sheet.points(models: models, copyIndex: 1) else { return nil }
            var score = 0
            if !tokens.isEmpty {
                let haystack = ([sheet.name, sheet.id] + sheet.keywords)
                    .joined(separator: " ")
                    .lowercased()
                score += tokens.filter { haystack.contains($0) }.count * 100
            }
            if sheet.characterRole != nil { score += 10 }
            if sheet.battleline { score += 5 }
            return Candidate(sheet: sheet, models: models, points: points, score: score)
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
