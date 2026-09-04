import Foundation

/// Deterministic 11th Edition army-construction validator.
///
/// Pure: `(list, catalog) -> ValidationResult`. No I/O, no SwiftUI.
enum ArmyListValidator {
    static func validate(list: ArmyListDocument, catalog: ArmyCatalog) -> ValidationResult {
        var issues: [ValidationIssue] = []

        if list.catalogVersion != catalog.version {
            issues.append(.init(
                code: "catalog.versionMismatch",
                severity: .warning,
                message: "List catalog \(list.catalogVersion) differs from loaded \(catalog.version). Re-check points."
            ))
        }

        guard let faction = catalog.faction(id: list.factionID) else {
            issues.append(.init(
                code: "faction.unknown",
                severity: .error,
                message: "Unknown faction “\(list.factionID)”."
            ))
            return ValidationResult(issues: issues, totalPoints: 0, detachmentPointsSpent: 0)
        }

        guard let battleSize = catalog.battleSize(id: list.battleSizeID) else {
            issues.append(.init(
                code: "battleSize.unknown",
                severity: .error,
                message: "Unknown battle size “\(list.battleSizeID)”."
            ))
            return ValidationResult(issues: issues, totalPoints: 0, detachmentPointsSpent: 0)
        }

        let dpSpent = validateDetachments(
            list: list,
            catalog: catalog,
            faction: faction,
            battleSize: battleSize,
            issues: &issues
        )

        let points = validateUnits(
            list: list,
            catalog: catalog,
            faction: faction,
            battleSize: battleSize,
            issues: &issues
        )

        validateWarlord(list: list, catalog: catalog, faction: faction, issues: &issues)

        if points > battleSize.pointsLimit {
            issues.append(.init(
                code: "points.overLimit",
                severity: .error,
                message: "List is \(points) pts; \(battleSize.name) limit is \(battleSize.pointsLimit)."
            ))
        } else if points == 0 && list.units.isEmpty {
            issues.append(.init(
                code: "list.empty",
                severity: .warning,
                message: "List has no units yet."
            ))
        }

        if dpSpent < battleSize.detachmentPointsBudget && !list.detachmentIDs.isEmpty {
            issues.append(.init(
                code: "dp.underBudget",
                severity: .warning,
                message: "Using \(dpSpent) of \(battleSize.detachmentPointsBudget) Detachment Points."
            ))
        }

        return ValidationResult(issues: issues, totalPoints: points, detachmentPointsSpent: dpSpent)
    }

    // MARK: - Detachments

    @discardableResult
    private static func validateDetachments(
        list: ArmyListDocument,
        catalog: ArmyCatalog,
        faction: FactionDefinition,
        battleSize: BattleSizeDefinition,
        issues: inout [ValidationIssue]
    ) -> Int {
        if list.detachmentIDs.isEmpty {
            issues.append(.init(
                code: "detachment.required",
                severity: .error,
                message: "Select at least one detachment."
            ))
            return 0
        }

        var spent = 0
        var seenTags: [String: String] = [:]
        var seenIDs = Set<String>()

        for id in list.detachmentIDs {
            if !seenIDs.insert(id).inserted {
                issues.append(.init(
                    code: "detachment.duplicate",
                    severity: .error,
                    message: "Detachment “\(id)” is selected more than once."
                ))
                continue
            }
            guard let detachment = catalog.detachment(id: id) else {
                issues.append(.init(
                    code: "detachment.unknown",
                    severity: .error,
                    message: "Unknown detachment “\(id)”."
                ))
                continue
            }
            if detachment.factionID != faction.id {
                issues.append(.init(
                    code: "detachment.wrongFaction",
                    severity: .error,
                    message: "\(detachment.name) is not a \(faction.name) detachment."
                ))
            }
            spent += detachment.detachmentPoints
            if let tag = detachment.uniqueTag {
                if let other = seenTags[tag] {
                    issues.append(.init(
                        code: "detachment.uniqueTagCollision",
                        severity: .error,
                        message: "\(detachment.name) and \(other) share unique tag “\(tag)”."
                    ))
                } else {
                    seenTags[tag] = detachment.name
                }
            }
        }

        if spent > battleSize.detachmentPointsBudget {
            issues.append(.init(
                code: "dp.overBudget",
                severity: .error,
                message: "Detachments cost \(spent) DP; \(battleSize.name) budget is \(battleSize.detachmentPointsBudget)."
            ))
        }

        return spent
    }

    // MARK: - Units

    private static func validateUnits(
        list: ArmyListDocument,
        catalog: ArmyCatalog,
        faction: FactionDefinition,
        battleSize: BattleSizeDefinition,
        issues: inout [ValidationIssue]
    ) -> Int {
        var totalPoints = 0
        var copyIndexByDatasheet: [String: Int] = [:]
        let unitByID = Dictionary(list.units.map { ($0.id, $0) }, uniquingKeysWith: { first, _ in first })
        if unitByID.count != list.units.count {
            issues.append(.init(
                code: "unit.duplicateID",
                severity: .error,
                message: "List contains duplicate unit instance IDs."
            ))
        }

        // Enhancement pick accounting: Upgrade enhancements sharing an id across
        // up to 3 units count as one pick.
        var enhancementPickSlots = 0
        var upgradeGroupsUsed: [String: Int] = [:]
        var enhancementsOnUnit: [UUID: Int] = [:]

        for unit in list.units {
            guard let sheet = catalog.datasheet(id: unit.datasheetID) else {
                issues.append(.init(
                    code: "unit.unknownDatasheet",
                    severity: .error,
                    message: "Unknown datasheet “\(unit.datasheetID)”.",
                    unitID: unit.id
                ))
                continue
            }

            if sheet.factionID != faction.id {
                issues.append(.init(
                    code: "unit.wrongFaction",
                    severity: .error,
                    message: "\(sheet.name) is not a \(faction.name) datasheet.",
                    unitID: unit.id
                ))
            }

            if !sheet.modelCounts.contains(unit.models)
                || unit.models < sheet.minModels
                || unit.models > sheet.maxModels
            {
                issues.append(.init(
                    code: "unit.modelCount",
                    severity: .error,
                    message: "\(sheet.name) cannot be taken at \(unit.models) models.",
                    unitID: unit.id
                ))
            }

            let nextCopy = (copyIndexByDatasheet[sheet.id] ?? 0) + 1
            copyIndexByDatasheet[sheet.id] = nextCopy

            if let pts = sheet.points(models: unit.models, copyIndex: nextCopy) {
                totalPoints += pts
                totalPoints += sheet.optionPoints(selectedIDs: unit.optionIDs)
            } else {
                issues.append(.init(
                    code: "unit.pointsMissing",
                    severity: .error,
                    message: "No points entry for \(sheet.name) at \(unit.models) models (copy #\(nextCopy)).",
                    unitID: unit.id
                ))
            }

            validateOptions(
                unit: unit,
                sheet: sheet,
                issues: &issues
            )

            // Attachment rules
            if sheet.mustAttach && unit.attachedToUnitID == nil {
                issues.append(.init(
                    code: "unit.mustAttach",
                    severity: .error,
                    message: "\(sheet.name) must be attached to a unit.",
                    unitID: unit.id
                ))
            }

            if let bodyID = unit.attachedToUnitID {
                guard let body = unitByID[bodyID] else {
                    issues.append(.init(
                        code: "unit.attachMissing",
                        severity: .error,
                        message: "\(sheet.name) attaches to a unit that is not on the list.",
                        unitID: unit.id
                    ))
                    continue
                }
                if body.id == unit.id {
                    issues.append(.init(
                        code: "unit.attachSelf",
                        severity: .error,
                        message: "\(sheet.name) cannot attach to itself.",
                        unitID: unit.id
                    ))
                }
                if sheet.characterRole == nil {
                    issues.append(.init(
                        code: "unit.attachNotCharacter",
                        severity: .error,
                        message: "\(sheet.name) cannot attach to another unit.",
                        unitID: unit.id
                    ))
                }
                // Empty leaderTo means this datasheet has no legal bodyguards in the
                // catalog. Do not treat that as "joins anything".
                if sheet.leaderTo.isEmpty {
                    issues.append(.init(
                        code: "unit.attachNoTargets",
                        severity: .error,
                        message: "\(sheet.name) has no Leader join targets in the catalog.",
                        unitID: unit.id
                    ))
                } else if !sheet.leaderTo.contains(body.datasheetID) {
                    let bodyName = catalog.datasheet(id: body.datasheetID)?.name ?? body.datasheetID
                    issues.append(.init(
                        code: "unit.attachIllegal",
                        severity: .error,
                        message: "\(sheet.name) cannot join \(bodyName).",
                        unitID: unit.id
                    ))
                }
            }

            // Enhancements on this unit
            enhancementsOnUnit[unit.id] = unit.enhancementIDs.count
            if unit.enhancementIDs.count > 1 {
                issues.append(.init(
                    code: "enhancement.onePerUnit",
                    severity: .error,
                    message: "\(sheet.name) has more than one enhancement.",
                    unitID: unit.id
                ))
            }
            for enhancementID in unit.enhancementIDs {
                guard let (detachment, enhancement) = catalog.enhancement(id: enhancementID) else {
                    issues.append(.init(
                        code: "enhancement.unknown",
                        severity: .error,
                        message: "Unknown enhancement “\(enhancementID)”.",
                        unitID: unit.id
                    ))
                    continue
                }
                if !list.detachmentIDs.contains(detachment.id) {
                    issues.append(.init(
                        code: "enhancement.detachmentNotSelected",
                        severity: .error,
                        message: "\(enhancement.name) requires \(detachment.name).",
                        unitID: unit.id
                    ))
                }
                if enhancement.isUpgrade {
                    if sheet.characterRole != nil {
                        issues.append(.init(
                            code: "enhancement.upgradeOnCharacter",
                            severity: .error,
                            message: "\(enhancement.name) is an Upgrade and cannot go on a Character.",
                            unitID: unit.id
                        ))
                    }
                    let count = (upgradeGroupsUsed[enhancement.id] ?? 0) + 1
                    upgradeGroupsUsed[enhancement.id] = count
                    if count == 1 {
                        enhancementPickSlots += 1
                    }
                    if count > 3 {
                        issues.append(.init(
                            code: "enhancement.upgradeCap",
                            severity: .error,
                            message: "\(enhancement.name) can be taken on at most three units.",
                            unitID: unit.id
                        ))
                    }
                } else {
                    if sheet.characterRole == nil {
                        issues.append(.init(
                            code: "enhancement.requiresCharacter",
                            severity: .error,
                            message: "\(enhancement.name) must go on a Character.",
                            unitID: unit.id
                        ))
                    }
                    enhancementPickSlots += 1
                }
                totalPoints += enhancement.points
            }
        }

        // Duplicate caps
        for (datasheetID, count) in copyIndexByDatasheet {
            guard let sheet = catalog.datasheet(id: datasheetID) else { continue }
            let limit: Int
            if let override = sheet.maxCopiesOverride {
                // Battle size may be smaller than the Strike Force-oriented BS max.
                let sizeLimit: Int
                if sheet.battleline {
                    sizeLimit = battleSize.battlelineDuplicateLimit
                } else if sheet.dedicatedTransport {
                    sizeLimit = battleSize.dedicatedTransportDuplicateLimit
                } else {
                    sizeLimit = battleSize.datasheetDuplicateLimit
                }
                limit = min(override, sizeLimit)
            } else if sheet.battleline {
                limit = battleSize.battlelineDuplicateLimit
            } else if sheet.dedicatedTransport {
                limit = battleSize.dedicatedTransportDuplicateLimit
            } else {
                limit = battleSize.datasheetDuplicateLimit
            }
            if sheet.epicHero && count > 1 {
                issues.append(.init(
                    code: "unit.epicHeroDuplicate",
                    severity: .error,
                    message: "\(sheet.name) is an Epic Hero and may only be taken once."
                ))
            } else if count > limit {
                issues.append(.init(
                    code: "unit.duplicateCap",
                    severity: .error,
                    message: "\(sheet.name) appears \(count) times; limit is \(limit) for \(battleSize.name)."
                ))
            }
        }

        // Attachment slot: one Leader + one Support/Character attach per bodyguard.
        var attachmentsByBody: [UUID: [ListUnitInstance]] = [:]
        for unit in list.units {
            if let body = unit.attachedToUnitID {
                attachmentsByBody[body, default: []].append(unit)
            }
        }
        for (bodyID, attached) in attachmentsByBody {
            let leaders = attached.filter {
                catalog.datasheet(id: $0.datasheetID)?.characterRole == .leader
            }
            let others = attached.filter {
                catalog.datasheet(id: $0.datasheetID)?.characterRole != .leader
            }
            if leaders.count > 1 {
                issues.append(.init(
                    code: "unit.leaderSlot",
                    severity: .error,
                    message: "A unit may only have one Leader attached.",
                    unitID: bodyID
                ))
            }
            if others.count > 1 {
                issues.append(.init(
                    code: "unit.supportSlot",
                    severity: .error,
                    message: "A unit may only have one Support/extra Character attached.",
                    unitID: bodyID
                ))
            }
        }

        if enhancementPickSlots > battleSize.enhancementPickLimit {
            issues.append(.init(
                code: "enhancement.pickLimit",
                severity: .error,
                message: "List uses \(enhancementPickSlots) enhancement picks; \(battleSize.name) allows \(battleSize.enhancementPickLimit)."
            ))
        }

        return totalPoints
    }

    // MARK: - Warlord

    private static func validateOptions(
        unit: ListUnitInstance,
        sheet: DatasheetDefinition,
        issues: inout [ValidationIssue]
    ) {
        guard !sheet.optionGroups.isEmpty else {
            if !unit.optionIDs.isEmpty {
                issues.append(.init(
                    code: "option.unknown",
                    severity: .warning,
                    message: "\(sheet.name) has loadout picks that are not in the catalog.",
                    unitID: unit.id
                ))
            }
            return
        }

        let knownIDs = Set(sheet.optionGroups.flatMap { $0.options.map(\.id) })
        for optionID in unit.optionIDs where !knownIDs.contains(optionID) {
            issues.append(.init(
                code: "option.unknown",
                severity: .warning,
                message: "\(sheet.name) has unknown loadout pick “\(optionID)”.",
                unitID: unit.id
            ))
        }

        for group in sheet.optionGroups {
            let groupIDs = Set(group.options.map(\.id))
            let selected = unit.optionIDs.filter { groupIDs.contains($0) }
            if selected.count < group.min || selected.count > group.max {
                issues.append(.init(
                    code: "option.groupCount",
                    severity: .warning,
                    message: "\(sheet.name): choose \(group.min)–\(group.max) from \(group.name) (have \(selected.count)).",
                    unitID: unit.id
                ))
            }
        }
    }

    private static func validateWarlord(
        list: ArmyListDocument,
        catalog: ArmyCatalog,
        faction: FactionDefinition,
        issues: inout [ValidationIssue]
    ) {
        guard let warlordID = list.warlordUnitID else {
            if !list.units.isEmpty {
                issues.append(.init(
                    code: "warlord.missing",
                    severity: .error,
                    message: "Choose a Warlord."
                ))
            }
            return
        }
        guard let unit = list.units.first(where: { $0.id == warlordID }) else {
            issues.append(.init(
                code: "warlord.missingUnit",
                severity: .error,
                message: "Warlord unit is not on the list."
            ))
            return
        }
        guard let sheet = catalog.datasheet(id: unit.datasheetID) else { return }
        if sheet.characterRole == nil {
            issues.append(.init(
                code: "warlord.notCharacter",
                severity: .error,
                message: "Warlord must be a Character (\(sheet.name) is not).",
                unitID: unit.id
            ))
        }
        let hasFactionKeyword = sheet.keywords.contains(where: { $0 == "Faction: \(faction.name)" })
            || sheet.factionID == faction.id
        if !hasFactionKeyword {
            issues.append(.init(
                code: "warlord.wrongFaction",
                severity: .error,
                message: "Warlord must have the \(faction.name) faction keyword.",
                unitID: unit.id
            ))
        }
    }
}
