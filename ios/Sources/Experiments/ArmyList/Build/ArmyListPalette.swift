import Foundation

/// Catalog-constrained moves the Army List construction loop can offer Laya.
///
/// Laya's ANE export is 96 tokens and 32 option slots. Construction uses at
/// most ``maxLayaOptions`` short options so the question head and a tiny
/// roster snapshot still fit.
enum ArmyListPalette {
    /// Options per Laya question. Eight short labels leave room for the state.
    static let maxLayaOptions = 8
    /// Stop filling when remaining points are at or below this and a Character
    /// is already on the list.
    static let goodEnoughSlack = 25
    /// Cap how many add steps one build or fill may take.
    static let maxAddSteps = 20

    /// Words too generic to steer unit selection.
    static let stopWords: Set<String> = [
        "the", "and", "with", "for", "list", "army", "only", "all",
        "some", "few", "lots", "many", "themed", "theme", "build",
        "make", "create", "using", "use", "from", "that", "this",
    ]

    /// One datasheet with the theme-and-role score used for shortlists.
    struct RankedSheet: Equatable {
        let sheet: DatasheetDefinition
        let score: Int
    }

    /// One legal enhancement on a specific unit that still has a pick slot.
    struct EnhancementMove: Equatable {
        let unitID: UUID
        let unitName: String
        let enhancement: EnhancementDefinition
        let points: Int
        let score: Int
        let label: String

        func option() -> LayaChoiceOption {
            LayaChoiceOption(label, "\(points)pt \(unitName)")
        }
    }

    /// One legal add: a datasheet at a model count that fits remaining points.
    struct AddMove: Equatable {
        let sheet: DatasheetDefinition
        let models: Int
        let points: Int
        let score: Int
        /// Unique choice label Laya returns.
        let label: String

        func option() -> LayaChoiceOption {
            var bits = ["\(points)pt"]
            if sheet.characterRole != nil { bits.append("Character") }
            if sheet.battleline { bits.append("Battleline") }
            if sheet.dedicatedTransport { bits.append("Transport") }
            return LayaChoiceOption(label, bits.joined(separator: " "))
        }
    }

    static func themeTokens(_ theme: String) -> [String] {
        theme
            .lowercased()
            .components(separatedBy: CharacterSet.alphanumerics.inverted)
            .map { $0.trimmingCharacters(in: .whitespaces) }
            .filter { $0.count >= 3 && !stopWords.contains($0) }
    }

    /// Theme hits, plus a small Character / Battleline nudge. Matches the
    /// ranking ``ArmyListStarterPrompt`` used for the AFM shortlist.
    static func themeScore(sheet: DatasheetDefinition, tokens: [String]) -> Int {
        var score = 0
        if !tokens.isEmpty {
            let haystack = ([sheet.name, sheet.id] + sheet.keywords + sheet.themeKeywords)
                .joined(separator: " ")
                .lowercased()
            score += tokens.filter { haystack.contains($0) }.count * 100
        }
        if sheet.characterRole != nil { score += 10 }
        if sheet.battleline { score += 5 }
        return score
    }

    static func hasBattleline(list: ArmyListDocument, catalog: ArmyCatalog) -> Bool {
        list.units.contains { catalog.datasheet(id: $0.datasheetID)?.battleline == true }
    }

    static func duplicateLimit(
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

    /// Points for a new copy at `models`, including default loadout picks.
    static func listCost(sheet: DatasheetDefinition, models: Int, copyIndex: Int) -> Int? {
        guard let pts = sheet.points(models: models, copyIndex: copyIndex) else { return nil }
        return pts + sheet.optionPoints(selectedIDs: sheet.defaultOptionIDs())
    }

    /// Faction datasheets that have at least one points entry, theme-ranked.
    static func rankedSheets(
        catalog: ArmyCatalog,
        factionID: String,
        theme: String
    ) -> [RankedSheet] {
        let tokens = themeTokens(theme)
        let eligible: [RankedSheet] = catalog.datasheets.compactMap { sheet in
            guard sheet.factionID == factionID, !sheet.legends else { return nil }
            let models = sheet.modelCounts.first ?? sheet.minModels
            guard sheet.points(models: models, copyIndex: 1) != nil else { return nil }
            return RankedSheet(sheet: sheet, score: themeScore(sheet: sheet, tokens: tokens))
        }
        return eligible.sorted { lhs, rhs in
            if lhs.score != rhs.score { return lhs.score > rhs.score }
            return lhs.sheet.name.localizedCaseInsensitiveCompare(rhs.sheet.name) == .orderedAscending
        }
    }

    /// Prompt line used by ``ArmyListStarterPrompt`` (id, name, pts, role, max).
    static func promptLine(sheet: DatasheetDefinition, battleSize: BattleSizeDefinition) -> String {
        var flags: [String] = []
        if sheet.characterRole != nil { flags.append("Character") }
        if sheet.battleline { flags.append("Battleline") }
        if sheet.dedicatedTransport { flags.append("Transport") }
        let role = flags.isEmpty ? "-" : flags.joined(separator: ",")
        let options = sheet.modelCounts.compactMap { models in
            guard let pts = sheet.points(models: models, copyIndex: 1) else { return nil }
            return "\(pts)@\(models)"
        }.joined(separator: ",")
        let maxCopies = duplicateLimit(for: sheet, battleSize: battleSize)
        return "\(sheet.id) | \(sheet.name) | \(options) | \(role) | \(maxCopies)"
    }

    static func legalDetachments(
        catalog: ArmyCatalog,
        factionID: String,
        dpBudget: Int,
        theme: String
    ) -> [DetachmentDefinition] {
        let tokens = themeTokens(theme)
        return catalog.detachments
            .filter { $0.factionID == factionID && $0.detachmentPoints <= dpBudget }
            .sorted { lhs, rhs in
                let ls = detachmentScore(lhs, tokens: tokens)
                let rs = detachmentScore(rhs, tokens: tokens)
                if ls != rs { return ls > rs }
                return lhs.name.localizedCaseInsensitiveCompare(rhs.name) == .orderedAscending
            }
    }

    private static func detachmentScore(_ detachment: DetachmentDefinition, tokens: [String]) -> Int {
        let hay = (detachment.name + " " + detachment.id + " " + detachment.forceDisposition).lowercased()
        let themeHits = tokens.filter { hay.contains($0) }.count
        return themeHits * 100 + detachment.detachmentPoints
    }

    /// Legal adds that fit remaining points and copy caps, best first.
    ///
    /// When `hasCharacter` is false, Characters that do not need a missing
    /// bodyguard rank first. When a Character is already on the list, extra
    /// Characters drop so greedy fill spends on troops.
    static func legalAdds(
        catalog: ArmyCatalog,
        list: ArmyListDocument,
        theme: String,
        remainingPoints: Int,
        hasCharacter: Bool,
        charactersOnly: Bool,
        limit: Int = maxLayaOptions
    ) -> [AddMove] {
        guard let battle = catalog.battleSize(id: list.battleSizeID) else { return [] }
        let tokens = themeTokens(theme)
        let needsBattleline = !hasBattleline(list: list, catalog: catalog)
        var moves: [AddMove] = []
        for sheet in catalog.datasheets {
            guard sheet.factionID == list.factionID, !sheet.legends else { continue }
            if charactersOnly, sheet.characterRole == nil { continue }
            if sheet.mustAttach, !hasLegalBodyguard(catalog: catalog, list: list, sheet: sheet) {
                continue
            }
            let copies = list.units.filter { $0.datasheetID == sheet.id }.count
            if sheet.epicHero, copies >= 1 { continue }
            let cap = duplicateLimit(for: sheet, battleSize: battle)
            if copies >= cap { continue }
            let copyIndex = copies + 1
            let fitting = sheet.modelCounts.compactMap { models -> (Int, Int)? in
                guard let cost = listCost(sheet: sheet, models: models, copyIndex: copyIndex),
                      cost <= remainingPoints
                else { return nil }
                return (models, cost)
            }
            guard let best = fitting.max(by: { $0.1 < $1.1 }) else { continue }
            var score = themeScore(sheet: sheet, tokens: tokens)
            if !hasCharacter, sheet.characterRole != nil {
                score += 1000
            }
            if hasCharacter, sheet.characterRole != nil {
                score -= 30
            }
            if needsBattleline, sheet.battleline {
                score += 220
            }
            score += best.1 / 25
            moves.append(
                AddMove(
                    sheet: sheet,
                    models: best.0,
                    points: best.1,
                    score: score,
                    label: defaultLabel(sheet: sheet, models: best.0)
                )
            )
        }
        moves.sort { lhs, rhs in
            if lhs.score != rhs.score { return lhs.score > rhs.score }
            return lhs.sheet.name.localizedCaseInsensitiveCompare(rhs.sheet.name) == .orderedAscending
        }
        return uniqued(Array(moves.prefix(limit)))
    }

    /// Enhancement pick slots the validator counts: each Character enhancement
    /// is one pick; each distinct Upgrade id is one pick (up to three copies).
    static func enhancementPickSlots(list: ArmyListDocument, catalog: ArmyCatalog) -> Int {
        var slots = 0
        var upgradeGroups = Set<String>()
        for unit in list.units {
            for enhancementID in unit.enhancementIDs {
                guard let (_, enhancement) = catalog.enhancement(id: enhancementID) else { continue }
                if enhancement.isUpgrade {
                    if upgradeGroups.insert(enhancement.id).inserted {
                        slots += 1
                    }
                } else {
                    slots += 1
                }
            }
        }
        return slots
    }

    static func upgradeCopies(list: ArmyListDocument, enhancementID: String) -> Int {
        list.units.reduce(0) { count, unit in
            count + (unit.enhancementIDs.contains(enhancementID) ? 1 : 0)
        }
    }

    /// Legal enhancement placements that fit remaining points and pick slots.
    static func legalEnhancements(
        catalog: ArmyCatalog,
        list: ArmyListDocument,
        theme: String,
        remainingPoints: Int,
        remainingPicks: Int,
        limit: Int = maxLayaOptions
    ) -> [EnhancementMove] {
        guard remainingPicks > 0, remainingPoints > 0 else { return [] }
        let tokens = themeTokens(theme)
        var moves: [EnhancementMove] = []
        for detachmentID in list.detachmentIDs {
            guard let detachment = catalog.detachment(id: detachmentID) else { continue }
            for enhancement in detachment.enhancements {
                if enhancement.points > remainingPoints { continue }
                let extraPick: Int
                if enhancement.isUpgrade {
                    let copies = upgradeCopies(list: list, enhancementID: enhancement.id)
                    if copies >= 3 { continue }
                    extraPick = copies == 0 ? 1 : 0
                } else {
                    extraPick = 1
                }
                if extraPick > remainingPicks { continue }
                for unit in list.units {
                    if !unit.enhancementIDs.isEmpty { continue }
                    guard let sheet = catalog.datasheet(id: unit.datasheetID) else { continue }
                    if enhancement.isUpgrade {
                        if sheet.characterRole != nil { continue }
                    } else if sheet.characterRole == nil {
                        continue
                    }
                    var score = tokens.filter { enhancement.name.lowercased().contains($0) }.count * 100
                    score += tokens.filter { sheet.name.lowercased().contains($0) }.count * 20
                    if list.warlordUnitID == unit.id { score += 40 }
                    score += enhancement.points / 10
                    moves.append(
                        EnhancementMove(
                            unitID: unit.id,
                            unitName: sheet.name,
                            enhancement: enhancement,
                            points: enhancement.points,
                            score: score,
                            label: enhancement.name
                        )
                    )
                }
            }
        }
        moves.sort { lhs, rhs in
            if lhs.score != rhs.score { return lhs.score > rhs.score }
            if lhs.points != rhs.points { return lhs.points < rhs.points }
            return lhs.enhancement.name.localizedCaseInsensitiveCompare(rhs.enhancement.name) == .orderedAscending
        }
        return uniquedEnhancements(Array(moves.prefix(limit)))
    }

    static func cheapestLegalAdd(
        catalog: ArmyCatalog,
        list: ArmyListDocument,
        remainingPoints: Int
    ) -> Int? {
        legalAdds(
            catalog: catalog,
            list: list,
            theme: "",
            remainingPoints: remainingPoints,
            hasCharacter: true,
            charactersOnly: false,
            limit: 512
        ).map(\.points).min()
    }

    static func hasCharacter(list: ArmyListDocument, catalog: ArmyCatalog) -> Bool {
        list.units.contains { catalog.datasheet(id: $0.datasheetID)?.characterRole != nil }
    }

    static func characters(on list: ArmyListDocument, catalog: ArmyCatalog) -> [ListUnitInstance] {
        list.units.filter { catalog.datasheet(id: $0.datasheetID)?.characterRole != nil }
    }

    static func hasLegalBodyguard(
        catalog: ArmyCatalog,
        list: ArmyListDocument,
        sheet: DatasheetDefinition
    ) -> Bool {
        !legalBodyguards(catalog: catalog, list: list, characterSheet: sheet).isEmpty
    }

    static func legalBodyguards(
        catalog: ArmyCatalog,
        list: ArmyListDocument,
        characterSheet: DatasheetDefinition
    ) -> [ListUnitInstance] {
        guard !characterSheet.leaderTo.isEmpty else { return [] }
        return list.units.filter { body in
            canAttach(characterSheet: characterSheet, to: body, list: list, catalog: catalog)
        }
    }

    static func canAttach(
        characterSheet: DatasheetDefinition,
        to body: ListUnitInstance,
        list: ArmyListDocument,
        catalog: ArmyCatalog
    ) -> Bool {
        guard characterSheet.leaderTo.contains(body.datasheetID) else { return false }
        let attached = list.units.filter { $0.attachedToUnitID == body.id }
        let leaders = attached.filter {
            catalog.datasheet(id: $0.datasheetID)?.characterRole == .leader
        }
        let others = attached.filter {
            catalog.datasheet(id: $0.datasheetID)?.characterRole != .leader
        }
        if characterSheet.characterRole == .leader {
            return leaders.isEmpty
        }
        return others.isEmpty
    }

    /// One line for the AFM-era starter prompt, plus a Character if the cut
    /// dropped every Character.
    static func promptSheets(
        catalog: ArmyCatalog,
        factionID: String,
        battleSize: BattleSizeDefinition,
        theme: String,
        limit: Int
    ) -> [DatasheetDefinition] {
        let ranked = rankedSheets(catalog: catalog, factionID: factionID, theme: theme)
        var chosen = Array(ranked.prefix(limit))
        if !chosen.contains(where: { $0.sheet.characterRole != nil }),
           let character = ranked.first(where: { $0.sheet.characterRole != nil })
        {
            if !chosen.isEmpty { chosen.removeLast() }
            chosen.append(character)
        }
        return chosen.map(\.sheet)
    }

    private static func defaultLabel(sheet: DatasheetDefinition, models: Int) -> String {
        if models == (sheet.modelCounts.first ?? sheet.minModels) {
            return sheet.name
        }
        return "\(sheet.name) \(models)"
    }

    private static func uniquedEnhancements(_ moves: [EnhancementMove]) -> [EnhancementMove] {
        var seen = Set<String>()
        return moves.map { move in
            var label = move.label
            if !seen.insert(label).inserted {
                label = "\(move.enhancement.name) · \(move.unitName)"
            }
            return EnhancementMove(
                unitID: move.unitID,
                unitName: move.unitName,
                enhancement: move.enhancement,
                points: move.points,
                score: move.score,
                label: label
            )
        }
    }

    private static func uniqued(_ moves: [AddMove]) -> [AddMove] {
        var seen = Set<String>()
        return moves.map { move in
            var label = move.label
            if !seen.insert(label).inserted {
                label = "\(move.sheet.id)@\(move.models)"
            }
            return AddMove(
                sheet: move.sheet,
                models: move.models,
                points: move.points,
                score: move.score,
                label: label
            )
        }
    }
}
