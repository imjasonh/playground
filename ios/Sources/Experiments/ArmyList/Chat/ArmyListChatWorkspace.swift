import Foundation

/// Shared mutable list the chat tools read and write.
///
/// Every mutation goes through this workspace so the UI and the on-device model
/// see the same document. Validation always uses `ArmyListValidator`.
@MainActor
final class ArmyListChatWorkspace: ObservableObject {
    @Published var list: ArmyListDocument
    let catalog: ArmyCatalog

    init(list: ArmyListDocument, catalog: ArmyCatalog) {
        self.list = list
        self.catalog = catalog
    }

    var validation: ValidationResult {
        ArmyListValidator.validate(list: list, catalog: catalog)
    }

    /// Replace the list document so `@Published` notifies observers.
    func replaceList(_ newList: ArmyListDocument) {
        var copy = newList
        copy.touch()
        list = copy
    }

    func compactSummary(maxIssues: Int = 12) -> String {
        let result = validation
        let text = ArmyListTextExporter.text(for: list, catalog: catalog, validation: result)
        // Cap issue dump for the model context.
        let lines = text.split(separator: "\n", omittingEmptySubsequences: false)
        var kept: [String] = []
        var issueCount = 0
        for line in lines {
            if line.hasPrefix("[ERROR]") || line.hasPrefix("[WARN]") {
                issueCount += 1
                if issueCount > maxIssues { continue }
            }
            kept.append(String(line))
        }
        if issueCount > maxIssues {
            kept.append("… \(issueCount - maxIssues) more issues omitted")
        }
        return kept.joined(separator: "\n")
    }
}

/// Pure tool implementations used by Foundation Models wrappers and unit tests.
@MainActor
enum ArmyListChatToolExecutor {
    static func getListSummary(workspace: ArmyListChatWorkspace) -> String {
        workspace.compactSummary()
    }

    static func searchCatalog(
        workspace: ArmyListChatWorkspace,
        query: String,
        kind: String
    ) -> String {
        let q = query.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        let kindNorm = kind.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        var lines: [String] = []

        let wantDetachments = kindNorm.isEmpty || kindNorm == "any" || kindNorm.contains("detach")
        let wantUnits = kindNorm.isEmpty || kindNorm == "any" || kindNorm.contains("unit")
            || kindNorm.contains("data")

        if wantDetachments {
            let matches = workspace.catalog.detachments.filter { detachment in
                detachment.factionID == workspace.list.factionID
                    && (q.isEmpty
                        || detachment.name.lowercased().contains(q)
                        || detachment.id.contains(q)
                        || detachment.forceDisposition.lowercased().contains(q))
            }
            for detachment in matches.prefix(12) {
                var line = "detachment \(detachment.id) | \(detachment.name) | \(detachment.detachmentPoints) DP | \(detachment.forceDisposition)"
                if let tag = detachment.uniqueTag {
                    line += " | unique:\(tag)"
                }
                lines.append(line)
            }
        }

        if wantUnits {
            let matches = workspace.catalog.datasheets.filter { sheet in
                sheet.factionID == workspace.list.factionID
                    && !sheet.legends
                    && (q.isEmpty
                        || sheet.name.lowercased().contains(q)
                        || sheet.id.contains(q)
                        || sheet.keywords.contains { $0.lowercased().contains(q) })
            }
            for sheet in matches.prefix(10) {
                let pts = sheet.points(models: sheet.minModels, copyIndex: 1).map(String.init) ?? "?"
                var flags: [String] = []
                if sheet.battleline { flags.append("Battleline") }
                if sheet.characterRole == .leader { flags.append("Leader") }
                if sheet.characterRole == .character { flags.append("Character") }
                if sheet.epicHero { flags.append("EpicHero") }
                if sheet.dedicatedTransport { flags.append("DedicatedTransport") }
                if sheet.legends { flags.append("Legends") }
                let flagText = flags.isEmpty ? "" : " | " + flags.joined(separator: ",")
                var copyNote = ""
                if let battle = workspace.catalog.battleSize(id: workspace.list.battleSizeID) {
                    let have = workspace.list.units.filter { $0.datasheetID == sheet.id }.count
                    let limit = duplicateLimit(for: sheet, battleSize: battle)
                    copyNote = " | copies \(have)/\(limit)"
                }
                lines.append(
                    "unit \(sheet.id) | \(sheet.name) | \(pts)pts@\(sheet.minModels)\(flagText)\(copyNote)"
                )
            }
        }

        if lines.isEmpty {
            return "No catalog matches for query “\(query)” kind “\(kind)”."
        }
        return lines.joined(separator: "\n")
    }

    static func setBattleSize(workspace: ArmyListChatWorkspace, battleSizeID: String) -> String {
        let id = resolveBattleSizeID(workspace: workspace, raw: battleSizeID)
        guard let size = workspace.catalog.battleSize(id: id) else {
            return "Unknown battle size “\(battleSizeID)”. Use incursion or strike-force."
        }
        var list = workspace.list
        list.battleSizeID = size.id
        workspace.replaceList(list)
        return mutationResult(workspace: workspace, note: "Battle size set to \(size.name) (\(size.pointsLimit) pts).")
    }

    /// Apply a full roster the model invented in one call (avoids addUnit context blowouts).
    ///
    /// `unitsCSV` entries are `datasheetIdOrName` or `datasheetIdOrName:models`, comma-separated.
    static func applyRosterPlan(
        workspace: ArmyListChatWorkspace,
        battleSizeID: String,
        detachmentIDsCSV: String,
        unitsCSV: String,
        listName: String
    ) -> String {
        let sizeID = resolveBattleSizeID(workspace: workspace, raw: battleSizeID)
        guard let size = workspace.catalog.battleSize(id: sizeID) else {
            return "Unknown battle size “\(battleSizeID)”. Use incursion or strike-force."
        }

        let rawDetachments = detachmentIDsCSV
            .split(separator: ",")
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { !$0.isEmpty }
        var detachmentIDs: [String] = []
        var unknownDetachments: [String] = []
        for raw in rawDetachments {
            if let id = resolveDetachmentID(workspace: workspace, raw: raw) {
                if !detachmentIDs.contains(id) {
                    detachmentIDs.append(id)
                }
            } else {
                unknownDetachments.append(raw)
            }
        }
        if detachmentIDs.isEmpty {
            return "No valid detachments in “\(detachmentIDsCSV)”. Call searchCatalog kind=detachment first."
        }

        let rawUnits = unitsCSV
            .split(separator: ",")
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { !$0.isEmpty }
        if rawUnits.isEmpty {
            return "unitsCSV is empty. Pass datasheet ids/names like shield-captain:1,custodian-guard:5."
        }

        var units: [ListUnitInstance] = []
        var unknownUnits: [String] = []
        var addedNotes: [String] = []
        for raw in rawUnits {
            let parts = raw.split(separator: ":", maxSplits: 1).map {
                $0.trimmingCharacters(in: .whitespacesAndNewlines)
            }
            let sheetRaw = parts[0]
            guard let sheet = resolveDatasheet(workspace: workspace, raw: sheetRaw) else {
                unknownUnits.append(sheetRaw)
                continue
            }
            let modelCount: Int
            if parts.count == 2, let parsed = Int(parts[1]), sheet.modelCounts.contains(parsed) {
                modelCount = parsed
            } else {
                modelCount = sheet.modelCounts.first ?? sheet.minModels
            }
            units.append(
                ListUnitInstance(
                    datasheetID: sheet.id,
                    models: modelCount,
                    optionIDs: sheet.defaultOptionIDs()
                )
            )
            addedNotes.append("\(sheet.name)×\(modelCount)")
        }
        if units.isEmpty {
            return "No valid units in unitsCSV. Unknown: \(unknownUnits.joined(separator: ", ")). Call searchCatalog."
        }

        var warlordID: UUID?
        if let character = units.first(where: {
            workspace.catalog.datasheet(id: $0.datasheetID)?.characterRole != nil
        }) {
            warlordID = character.id
        }

        let trimmedName = listName.trimmingCharacters(in: .whitespacesAndNewlines)
        var list = workspace.list
        list.battleSizeID = size.id
        list.detachmentIDs = detachmentIDs
        list.units = units
        list.warlordUnitID = warlordID
        if !trimmedName.isEmpty {
            list.name = trimmedName
        }
        // Drop enhancements that no longer apply.
        for index in list.units.indices {
            list.units[index].enhancementIDs.removeAll { enhancementID in
                guard let (detachment, _) = workspace.catalog.enhancement(id: enhancementID) else {
                    return true
                }
                return !detachmentIDs.contains(detachment.id)
            }
        }
        workspace.replaceList(list)

        var note = "Applied roster (\(addedNotes.joined(separator: ", "))) · \(size.name)."
        if !unknownDetachments.isEmpty {
            note += " Unknown detachments ignored: \(unknownDetachments.joined(separator: ", "))."
        }
        if !unknownUnits.isEmpty {
            note += " Unknown units ignored: \(unknownUnits.joined(separator: ", "))."
        }
        return mutationResult(workspace: workspace, note: note)
    }

    static func setDetachments(workspace: ArmyListChatWorkspace, detachmentIDsCSV: String) -> String {
        let rawIDs = detachmentIDsCSV
            .split(separator: ",")
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { !$0.isEmpty }
        var resolved: [String] = []
        var unknown: [String] = []
        for raw in rawIDs {
            if let id = resolveDetachmentID(workspace: workspace, raw: raw) {
                if !resolved.contains(id) {
                    resolved.append(id)
                }
            } else {
                unknown.append(raw)
            }
        }
        var list = workspace.list
        list.detachmentIDs = resolved
        // Drop enhancements that no longer belong to a selected detachment.
        for index in list.units.indices {
            list.units[index].enhancementIDs.removeAll { enhancementID in
                guard let (detachment, _) = workspace.catalog.enhancement(id: enhancementID) else {
                    return true
                }
                return !resolved.contains(detachment.id)
            }
        }
        workspace.replaceList(list)
        var note = "Detachments set to: \(resolved.joined(separator: ", "))."
        if !unknown.isEmpty {
            note += " Unknown ignored: \(unknown.joined(separator: ", "))."
        }
        return mutationResult(workspace: workspace, note: note)
    }

    static func addUnit(
        workspace: ArmyListChatWorkspace,
        datasheetID: String,
        models: Double
    ) -> String {
        guard let sheet = resolveDatasheet(workspace: workspace, raw: datasheetID) else {
            return "Unknown datasheet “\(datasheetID)”. Call searchCatalog first."
        }
        guard let battle = workspace.catalog.battleSize(id: workspace.list.battleSizeID) else {
            return "Unknown battle size on the list."
        }
        let existingCopies = workspace.list.units.filter { $0.datasheetID == sheet.id }.count
        let nextCopy = existingCopies + 1
        let limit = duplicateLimit(for: sheet, battleSize: battle)
        if sheet.epicHero && nextCopy > 1 {
            return "Rejected: \(sheet.name) is an Epic Hero (max 1). Status unchanged."
        }
        if nextCopy > limit {
            return "Rejected: \(sheet.name) already has \(existingCopies)/\(limit) copies for \(battle.name). Pick a different datasheet. Status unchanged."
        }

        let requested = Int(models.rounded())
        let modelCount: Int
        if sheet.modelCounts.contains(requested) {
            modelCount = requested
        } else {
            modelCount = sheet.modelCounts.first ?? sheet.minModels
        }
        guard let cost = sheet.points(models: modelCount, copyIndex: nextCopy) else {
            return "Rejected: no points entry for \(sheet.name) ×\(modelCount)."
        }
        let remaining = battle.pointsLimit - workspace.validation.totalPoints
        if cost > remaining {
            return "Rejected: \(sheet.name) ×\(modelCount) is \(cost) pts but only \(remaining) pts remain under \(battle.pointsLimit). Status unchanged."
        }

        let unit = ListUnitInstance(
            datasheetID: sheet.id,
            models: modelCount,
            optionIDs: sheet.defaultOptionIDs()
        )
        var list = workspace.list
        list.units.append(unit)
        if list.warlordUnitID == nil, sheet.characterRole != nil {
            list.warlordUnitID = unit.id
        }
        workspace.replaceList(list)
        return mutationResult(
            workspace: workspace,
            note: "Added \(sheet.name) ×\(modelCount) (id \(unit.id.uuidString))."
        )
    }

    static func removeUnit(workspace: ArmyListChatWorkspace, unitID: String) -> String {
        guard let id = UUID(uuidString: unitID),
              let index = workspace.list.units.firstIndex(where: { $0.id == id })
        else {
            return "No unit with id “\(unitID)”."
        }
        var list = workspace.list
        let removed = list.units.remove(at: index)
        list.units = list.units.map { unit in
            var copy = unit
            if copy.attachedToUnitID == id {
                copy.attachedToUnitID = nil
            }
            return copy
        }
        if list.warlordUnitID == id {
            list.warlordUnitID = nil
        }
        workspace.replaceList(list)
        let name = workspace.catalog.datasheet(id: removed.datasheetID)?.name ?? removed.datasheetID
        return mutationResult(workspace: workspace, note: "Removed \(name).")
    }

    static func setUnitModels(
        workspace: ArmyListChatWorkspace,
        unitID: String,
        models: Double
    ) -> String {
        guard let id = UUID(uuidString: unitID),
              let index = workspace.list.units.firstIndex(where: { $0.id == id }),
              let sheet = workspace.catalog.datasheet(id: workspace.list.units[index].datasheetID)
        else {
            return "No unit with id “\(unitID)”."
        }
        let requested = Int(models.rounded())
        guard sheet.modelCounts.contains(requested) else {
            return "\(sheet.name) allows model counts \(sheet.modelCounts), not \(requested)."
        }
        var list = workspace.list
        list.units[index].models = requested
        workspace.replaceList(list)
        return mutationResult(workspace: workspace, note: "Set \(sheet.name) to \(requested) models.")
    }

    static func attachCharacter(
        workspace: ArmyListChatWorkspace,
        characterUnitID: String,
        bodyUnitID: String
    ) -> String {
        let bodyRaw = bodyUnitID.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        guard let charID = UUID(uuidString: characterUnitID),
              let charIndex = workspace.list.units.firstIndex(where: { $0.id == charID })
        else {
            return "No character unit id “\(characterUnitID)”."
        }
        var list = workspace.list
        if bodyRaw.isEmpty || bodyRaw == "none" || bodyRaw == "nil" {
            list.units[charIndex].attachedToUnitID = nil
            workspace.replaceList(list)
            return mutationResult(workspace: workspace, note: "Detached character from any unit.")
        }
        guard let bodyID = UUID(uuidString: bodyUnitID),
              list.units.contains(where: { $0.id == bodyID })
        else {
            return "No bodyguard unit id “\(bodyUnitID)”."
        }
        list.units[charIndex].attachedToUnitID = bodyID
        workspace.replaceList(list)
        return mutationResult(workspace: workspace, note: "Attached character to \(bodyID.uuidString).")
    }

    static func setWarlord(workspace: ArmyListChatWorkspace, unitID: String) -> String {
        let raw = unitID.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        var list = workspace.list
        if raw.isEmpty || raw == "none" || raw == "nil" {
            list.warlordUnitID = nil
            workspace.replaceList(list)
            return mutationResult(workspace: workspace, note: "Cleared Warlord.")
        }
        guard let id = UUID(uuidString: unitID),
              list.units.contains(where: { $0.id == id })
        else {
            return "No unit id “\(unitID)” on the list."
        }
        list.warlordUnitID = id
        workspace.replaceList(list)
        return mutationResult(workspace: workspace, note: "Warlord set to \(id.uuidString).")
    }

    static func setListName(workspace: ArmyListChatWorkspace, name: String) -> String {
        let trimmed = name.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            return "Name cannot be empty."
        }
        var list = workspace.list
        list.name = trimmed
        workspace.replaceList(list)
        return mutationResult(workspace: workspace, note: "List renamed to “\(trimmed)”.")
    }

    static func setEnhancement(
        workspace: ArmyListChatWorkspace,
        unitID: String,
        enhancementID: String
    ) -> String {
        guard let id = UUID(uuidString: unitID),
              let index = workspace.list.units.firstIndex(where: { $0.id == id })
        else {
            return "No unit id “\(unitID)”."
        }
        let raw = enhancementID.trimmingCharacters(in: .whitespacesAndNewlines)
        var list = workspace.list
        if raw.isEmpty || raw.lowercased() == "none" || raw.lowercased() == "nil" {
            list.units[index].enhancementIDs = []
            workspace.replaceList(list)
            return mutationResult(workspace: workspace, note: "Cleared enhancements on unit.")
        }
        guard let resolved = resolveEnhancementID(workspace: workspace, raw: raw) else {
            return "Unknown enhancement “\(enhancementID)”. Use detachmentId--enhancement-slug ids from the catalog."
        }
        list.units[index].enhancementIDs = [resolved]
        workspace.replaceList(list)
        return mutationResult(workspace: workspace, note: "Set enhancement \(resolved).")
    }

    static func clearUnits(workspace: ArmyListChatWorkspace) -> String {
        var list = workspace.list
        list.units = []
        list.warlordUnitID = nil
        workspace.replaceList(list)
        return mutationResult(workspace: workspace, note: "Cleared all units.")
    }

    // MARK: - Helpers

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

    private static func mutationResult(workspace: ArmyListChatWorkspace, note: String) -> String {
        let result = workspace.validation
        let status = result.isLegal ? "LEGAL" : "ILLEGAL"
        var lines = [
            note,
            "Status: \(status) · \(result.totalPoints) pts · DP \(result.detachmentPointsSpent) · units=\(workspace.list.units.count)",
            "errors=\(result.errors.count) warnings=\(result.warnings.count)",
        ]
        for issue in result.issues.prefix(6) {
            let mark = issue.severity == .error ? "ERROR" : "WARN"
            lines.append("[\(mark)] \(issue.code): \(issue.message)")
        }
        // Keep mutation replies short — a full roster dump after every addUnit
        // blows the on-device 4k context window mid-build.
        return lines.joined(separator: "\n")
    }

    private static func resolveBattleSizeID(workspace: ArmyListChatWorkspace, raw: String) -> String {
        let q = raw.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        if let exact = workspace.catalog.battleSizes.first(where: { $0.id == q }) {
            return exact.id
        }
        if q.contains("1000") || q.contains("incursion") { return "incursion" }
        if q.contains("2000") || q.contains("strike") { return "strike-force" }
        return q
    }

    private static func resolveDetachmentID(workspace: ArmyListChatWorkspace, raw: String) -> String? {
        let q = raw.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        if let exact = workspace.catalog.detachment(id: q), exact.factionID == workspace.list.factionID {
            return exact.id
        }
        let factionDetachments = workspace.catalog.detachments.filter {
            $0.factionID == workspace.list.factionID
        }
        if let suffix = factionDetachments.first(where: { $0.id.hasSuffix("--\(q)") || $0.id == q }) {
            return suffix.id
        }
        let matches = factionDetachments.filter {
            $0.id.contains(q) || $0.name.lowercased().contains(q)
        }
        return matches.count == 1 ? matches[0].id : nil
    }

    private static func resolveDatasheet(workspace: ArmyListChatWorkspace, raw: String) -> DatasheetDefinition? {
        let q = raw.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        if let exact = workspace.catalog.datasheet(id: q), exact.factionID == workspace.list.factionID {
            return exact
        }
        let factionSheets = workspace.catalog.datasheets.filter {
            $0.factionID == workspace.list.factionID
        }
        if let suffix = factionSheets.first(where: { $0.id.hasSuffix("--\(q)") || $0.id == q }) {
            return suffix
        }
        let matches = factionSheets.filter {
            $0.id.contains(q) || $0.name.lowercased().contains(q)
        }
        if matches.count == 1 { return matches[0] }
        return nil
    }

    private static func resolveEnhancementID(workspace: ArmyListChatWorkspace, raw: String) -> String? {
        let q = raw.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        if workspace.catalog.enhancement(id: q) != nil { return q }
        // Allow bare slug if unique among selected detachments.
        var hits: [String] = []
        for detachmentID in workspace.list.detachmentIDs {
            guard let detachment = workspace.catalog.detachment(id: detachmentID) else { continue }
            for enhancement in detachment.enhancements {
                if enhancement.id == q || enhancement.id.hasSuffix("--\(q)") || enhancement.name.lowercased() == q {
                    hits.append(enhancement.id)
                }
            }
        }
        return hits.count == 1 ? hits[0] : nil
    }
}
