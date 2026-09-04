import Foundation

/// Builds a legal-ish starter list for the current faction and battle size.
///
/// Used by List chat so "Build 1k" is one tool call instead of a long
/// addUnit loop that blows the on-device context window.
enum ArmyListLegalSeeder {
    struct Result: Equatable {
        var list: ArmyListDocument
        var validation: ValidationResult
        var notes: String
    }

    static func seed(
        catalog: ArmyCatalog,
        factionID: String,
        battleSizeID: String,
        name: String? = nil
    ) -> Result? {
        guard let faction = catalog.faction(id: factionID),
              let battle = catalog.battleSize(id: battleSizeID)
        else {
            return nil
        }

        let sheets = catalog.datasheets.filter {
            $0.factionID == factionID && !$0.legends
        }
        let detachments = catalog.detachments.filter { $0.factionID == factionID }
        guard !detachments.isEmpty else {
            return nil
        }

        let combo = bestDetachmentCombo(
            detachments,
            budget: battle.detachmentPointsBudget
        )
        guard !combo.isEmpty,
              let warlordPick = pickWarlord(sheets)
        else {
            return nil
        }
        var units: [ListUnitInstance] = []
        var copies: [String: Int] = [:]
        var points = 0
        let limit = battle.pointsLimit
        let target = Int(Double(limit) * 0.88)

        var warlord = ListUnitInstance(
            datasheetID: warlordPick.id,
            models: warlordPick.minModels,
            optionIDs: warlordPick.defaultOptionIDs()
        )
        let warlordCost = warlordPick.points(models: warlord.models, copyIndex: 1) ?? 0
        // Skip characters with no points entry — they break legality/points.
        guard warlordCost > 0 || warlordPick.points(models: warlord.models, copyIndex: 1) != nil else {
            return nil
        }
        units.append(warlord)
        copies[warlordPick.id, default: 0] += 1
        points += warlordCost

        func canAdd(sheet: DatasheetDefinition, models: Int) -> Int? {
            let nextCopy = (copies[sheet.id] ?? 0) + 1
            if sheet.epicHero && nextCopy > 1 { return nil }
            let sizeLimit: Int
            if sheet.battleline {
                sizeLimit = battle.battlelineDuplicateLimit
            } else if sheet.dedicatedTransport {
                sizeLimit = battle.dedicatedTransportDuplicateLimit
            } else {
                sizeLimit = battle.datasheetDuplicateLimit
            }
            let lim = sheet.maxCopiesOverride.map { min($0, sizeLimit) } ?? sizeLimit
            if nextCopy > lim { return nil }
            guard let cost = sheet.points(models: models, copyIndex: nextCopy) else { return nil }
            if points + cost > limit { return nil }
            return cost
        }

        // Prefer a legal attach body for the warlord before other fillers.
        var bodyForAttach: ListUnitInstance?
        for targetID in warlordPick.leaderTo {
            guard let sheet = sheets.first(where: { $0.id == targetID }) else { continue }
            guard let cost = canAdd(sheet: sheet, models: sheet.minModels) else { continue }
            let body = ListUnitInstance(
                datasheetID: sheet.id,
                models: sheet.minModels,
                optionIDs: sheet.defaultOptionIDs()
            )
            units.append(body)
            copies[sheet.id, default: 0] += 1
            points += cost
            warlord.attachedToUnitID = body.id
            units[0] = warlord
            bodyForAttach = body
            break
        }

        let battleline = sheets.filter(\.battleline)
        var fillers = sheets.filter { $0.characterRole == nil && !$0.epicHero }
        fillers.sort {
            ($0.points(models: $0.minModels, copyIndex: 1) ?? 9_999)
                < ($1.points(models: $1.minModels, copyIndex: 1) ?? 9_999)
        }
        let pool = battleline + fillers

        for sheet in pool {
            if points >= target { break }
            var modelOpts = sheet.modelCounts
            if sheet.battleline {
                modelOpts.sort(by: >)
            }
            for models in modelOpts {
                guard let cost = canAdd(sheet: sheet, models: models) else { continue }
                let unit = ListUnitInstance(
                    datasheetID: sheet.id,
                    models: models,
                    optionIDs: sheet.defaultOptionIDs()
                )
                units.append(unit)
                copies[sheet.id, default: 0] += 1
                points += cost
                if bodyForAttach == nil {
                    bodyForAttach = unit
                }
                break
            }
        }

        if warlord.attachedToUnitID == nil, let body = bodyForAttach, !warlordPick.leaderTo.isEmpty {
            if warlordPick.leaderTo.contains(body.datasheetID) {
                warlord.attachedToUnitID = body.id
                units[0] = warlord
            } else if let existing = units.first(where: {
                $0.id != warlord.id && warlordPick.leaderTo.contains($0.datasheetID)
            }) {
                warlord.attachedToUnitID = existing.id
                units[0] = warlord
            }
        }

        for sheet in fillers where points < target {
            guard let cost = canAdd(sheet: sheet, models: sheet.minModels) else { continue }
            units.append(
                ListUnitInstance(
                    datasheetID: sheet.id,
                    models: sheet.minModels,
                    optionIDs: sheet.defaultOptionIDs()
                )
            )
            copies[sheet.id, default: 0] += 1
            points += cost
        }

        let listName = name?.trimmingCharacters(in: .whitespacesAndNewlines).nilIfEmpty
            ?? "\(faction.name) \(battle.name)"
        let list = ArmyListDocument(
            name: listName,
            catalogVersion: catalog.version,
            factionID: factionID,
            battleSizeID: battleSizeID,
            detachmentIDs: combo.map(\.id),
            units: units,
            warlordUnitID: warlord.id
        )
        let validation = ArmyListValidator.validate(list: list, catalog: catalog)
        return Result(
            list: list,
            validation: validation,
            notes: "Seeded \(units.count) units · \(combo.map(\.name).joined(separator: ", "))"
        )
    }

    /// Prefer a non-epic Leader that can join Battleline; avoid epic heroes like Aleya/Trajann.
    private static func pickWarlord(_ sheets: [DatasheetDefinition]) -> DatasheetDefinition? {
        let leaders = sheets.filter { $0.characterRole == .leader && !$0.epicHero }
        let withBattlelineJoin = leaders.filter { sheet in
            sheet.leaderTo.contains { target in
                sheets.contains { $0.id == target && $0.battleline }
            }
        }
        if let pick = withBattlelineJoin.first {
            return pick
        }
        if let pick = leaders.first {
            return pick
        }
        return sheets.first { $0.characterRole != nil && !$0.epicHero }
            ?? sheets.first { $0.characterRole != nil }
    }

    /// Prefer one detachment that spends as much of the DP budget as possible.
    private static func bestDetachmentCombo(
        _ detachments: [DetachmentDefinition],
        budget: Int
    ) -> [DetachmentDefinition] {
        let sorted = detachments.sorted {
            if $0.detachmentPoints != $1.detachmentPoints {
                return $0.detachmentPoints > $1.detachmentPoints
            }
            return $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending
        }
        if let single = sorted.first(where: { $0.detachmentPoints <= budget }) {
            return [single]
        }
        // Greedy pack of cheapest unique-tag-safe detachments.
        let cheapFirst = detachments.sorted {
            if $0.detachmentPoints != $1.detachmentPoints {
                return $0.detachmentPoints < $1.detachmentPoints
            }
            return $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending
        }
        var picked: [DetachmentDefinition] = []
        var spent = 0
        var usedTags: Set<String> = []
        for det in cheapFirst {
            if spent + det.detachmentPoints > budget { continue }
            if let tag = det.uniqueTag, usedTags.contains(tag) { continue }
            picked.append(det)
            spent += det.detachmentPoints
            if let tag = det.uniqueTag { usedTags.insert(tag) }
        }
        return picked
    }
}

private extension String {
    var nilIfEmpty: String? {
        isEmpty ? nil : self
    }
}
