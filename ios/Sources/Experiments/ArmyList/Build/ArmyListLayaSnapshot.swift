import Foundation

/// Compact roster text for a Laya question. The ANE sequence is 96 tokens, so
/// this stays to faction, spend, a few unit names, and remaining points.
enum ArmyListLayaSnapshot {
    static let maxCharacters = 280

    static func text(
        list: ArmyListDocument,
        catalog: ArmyCatalog,
        theme: String,
        validation: ValidationResult? = nil
    ) -> String {
        let faction = catalog.faction(id: list.factionID)?.name ?? list.factionID
        let battle = catalog.battleSize(id: list.battleSizeID)
        let battleName = battle?.name ?? list.battleSizeID
        let limit = battle?.pointsLimit ?? 0
        let result = validation ?? ArmyListValidator.validate(list: list, catalog: catalog)
        let remaining = max(0, limit - result.totalPoints)
        let themeBit = theme.trimmingCharacters(in: .whitespacesAndNewlines)
        var parts: [String] = [
            "\(faction) \(battleName) \(limit).",
        ]
        if !themeBit.isEmpty {
            parts.append("Theme \(themeBit).")
        }
        parts.append("\(result.totalPoints)/\(limit) pts, \(result.detachmentPointsSpent) DP.")
        let names = list.units.prefix(6).map { unit in
            let name = catalog.datasheet(id: unit.datasheetID)?.name ?? unit.datasheetID
            return unit.models > 1 ? "\(name)×\(unit.models)" : name
        }
        if names.isEmpty {
            parts.append("Roster empty.")
        } else {
            var roster = "Roster: " + names.joined(separator: ", ")
            if list.units.count > names.count {
                roster += " +\(list.units.count - names.count)"
            }
            parts.append(roster + ".")
        }
        parts.append("Remaining \(remaining).")
        if ArmyListPalette.hasCharacter(list: list, catalog: catalog) {
            parts.append("Has Character.")
        } else {
            parts.append("Need Character.")
        }
        if let error = result.errors.first {
            parts.append("Issue \(error.code).")
        }
        let joined = parts.joined(separator: " ")
        if joined.count <= maxCharacters {
            return joined
        }
        return String(joined.prefix(maxCharacters))
    }
}
