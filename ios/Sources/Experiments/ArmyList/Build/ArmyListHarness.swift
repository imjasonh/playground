import Foundation

/// Routes one construction question to the cheapest worker that can answer.
///
/// The Army List controller is the harness. Mechanical catalog code lists legal
/// moves, applies picks, re-validates, and answers when only one option remains.
/// Laya answers labeled choices (including model counts and optional attaches),
/// leftover yes/no, and a post-pass theme score. Apple Intelligence writes the
/// theme brief and a list name once per Build / Fill. Workers do not call each
/// other.
@MainActor
enum ArmyListHarness {
    enum Worker: String, Equatable {
        case mechanical
        case laya
        case foundationModels

        /// Short status label for the last construction step.
        var displayName: String {
            switch self {
            case .mechanical: return "Catalog"
            case .laya: return "Laya"
            case .foundationModels: return "Apple Intelligence"
            }
        }
    }

    /// Laya score legend for "how on-theme is this roster?"
    static let themeScoreLevels = ["off-theme", "weak", "mixed", "strong", "exact"]

    /// Leftover-point band where Laya may stop adding instead of stuffing units.
    static let keepAddingBand = 80

    /// Laya choice only when the graph is loaded and two or more options
    /// remain. One legal move, or greedy fill, is catalog work.
    static func choiceWorker(optionCount: Int, usedLaya: Bool = true) -> Worker {
        optionCount >= 2 && usedLaya ? .laya : .mechanical
    }

    /// True when leftover points sit above slack but still in the small band,
    /// so Laya can say the list is complete.
    static func shouldAskToKeepAdding(
        hasCharacter: Bool,
        remainingPoints: Int,
        cheapestLegal: Int?
    ) -> Bool {
        guard hasCharacter else { return false }
        if remainingPoints <= ArmyListPalette.goodEnoughSlack { return false }
        if let cheapestLegal, remainingPoints < cheapestLegal { return false }
        return remainingPoints <= keepAddingBand
    }

    /// If any candidate hits theme tokens, drop the rest. Empty tokens, or no
    /// hits, leave the pool unchanged so a later Laya yes/no can still handle
    /// AFM words the catalog does not spell.
    static func preferThemed<T>(
        _ items: [T],
        tokens: [String],
        matches: (T) -> Bool
    ) -> [T] {
        if tokens.isEmpty { return items }
        let hits = items.filter(matches)
        return hits.isEmpty ? items : hits
    }

    /// Enhancement / detachment names use the same overlap rule.
    static func textMatchesTheme(_ text: String, tokens: [String]) -> Bool {
        tokens.isEmpty || tokens.contains { token in
            text.lowercased().contains(token)
        }
    }

    /// How to accept a candidate against the brief.
    enum ThemeRoute: Equatable {
        /// No theme, or the datasheet already matches tokens.
        case accept
        /// Ask Laya whether a non-matching candidate still fits.
        case askLaya
        /// No Laya, and the datasheet misses every token.
        case reject
    }

    static func themeRoute(
        sheet: DatasheetDefinition,
        tokens: [String],
        usedLaya: Bool,
        requireCharacter: Bool,
        remainingAlternatives: Int
    ) -> ThemeRoute {
        if tokens.isEmpty { return .accept }
        if ArmyListPalette.matchesTheme(sheet: sheet, tokens: tokens) { return .accept }
        if usedLaya { return .askLaya }
        if requireCharacter, remainingAlternatives == 0 { return .accept }
        return .reject
    }

    /// Units the points-cut step may drop: not the warlord, not the last
    /// Character. Lowest theme overlap first, then highest points.
    static func cutCandidates(
        list: ArmyListDocument,
        catalog: ArmyCatalog,
        tokens: [String],
        limit: Int
    ) -> [ListUnitInstance] {
        let characters = list.units.filter { unit in
            catalog.datasheet(id: unit.datasheetID)?.characterRole != nil
        }
        let warlord = list.warlordUnitID
        let removable = list.units.filter { unit in
            if let warlord, unit.id == warlord { return false }
            if characters.count == 1, characters[0].id == unit.id { return false }
            return true
        }
        let ranked = removable.sorted { lhs, rhs in
            let leftHits = themeHits(unit: lhs, catalog: catalog, tokens: tokens)
            let rightHits = themeHits(unit: rhs, catalog: catalog, tokens: tokens)
            if leftHits != rightHits { return leftHits < rightHits }
            let leftPts = points(unit: lhs, catalog: catalog)
            let rightPts = points(unit: rhs, catalog: catalog)
            if leftPts != rightPts { return leftPts > rightPts }
            return lhs.datasheetID < rhs.datasheetID
        }
        return Array(ranked.prefix(limit))
    }

    static func stampedChoice(label: String, options: [LayaChoiceOption]? = nil) -> LayaDecision {
        let opts = options ?? [LayaChoiceOption(label)]
        return LayaGreedyDecider.choice(label: label, options: opts, act: 1)
    }

    static func scoreLegendLabel(_ decision: LayaDecision) -> String {
        guard case .score(let value, _, let legend) = decision.answer, !legend.isEmpty else {
            return "unknown"
        }
        let index = min(max(Int(value.rounded()), 0), legend.count - 1)
        return legend[index]
    }

    private static func themeHits(
        unit: ListUnitInstance,
        catalog: ArmyCatalog,
        tokens: [String]
    ) -> Int {
        guard let sheet = catalog.datasheet(id: unit.datasheetID) else { return 0 }
        return ArmyListPalette.themeHitCount(sheet: sheet, tokens: tokens)
    }

    private static func points(unit: ListUnitInstance, catalog: ArmyCatalog) -> Int {
        guard let sheet = catalog.datasheet(id: unit.datasheetID) else { return 0 }
        return sheet.points(models: unit.models, copyIndex: 1) ?? 0
    }
}
