import Foundation

extension ArmyListDocument {
    /// Remaps datasheet / detachment / enhancement ids through the catalog's
    /// migration table, then bumps `catalogVersion` when the list no longer
    /// references unknown construction ids.
    ///
    /// Returns `true` when the document changed and should be persisted.
    @discardableResult
    mutating func applyCatalogUpgrade(using catalog: ArmyCatalog) -> Bool {
        var changed = false

        let remappedDetachments = detachmentIDs.map { catalog.migratedID($0) }
        if remappedDetachments != detachmentIDs {
            detachmentIDs = remappedDetachments
            changed = true
        }

        var remappedUnits: [ListUnitInstance] = []
        remappedUnits.reserveCapacity(units.count)
        for unit in units {
            var next = unit
            let sheetID = catalog.migratedID(unit.datasheetID)
            if sheetID != unit.datasheetID {
                next.datasheetID = sheetID
                changed = true
            }
            let enhancementIDs = unit.enhancementIDs.map { catalog.migratedID($0) }
            if enhancementIDs != unit.enhancementIDs {
                next.enhancementIDs = enhancementIDs
                changed = true
            }
            remappedUnits.append(next)
        }
        if remappedUnits != units {
            units = remappedUnits
            changed = true
        }

        guard catalogVersion != catalog.version else {
            return changed
        }

        let validation = ArmyListValidator.validate(list: self, catalog: catalog)
        let hasUnknownConstructionIDs = validation.issues.contains { issue in
            switch issue.code {
            case "unit.unknownDatasheet",
                 "enhancement.unknown",
                 "detachment.unknown",
                 "faction.unknown",
                 "battleSize.unknown":
                return true
            default:
                return false
            }
        }
        if !hasUnknownConstructionIDs {
            catalogVersion = catalog.version
            changed = true
        }
        return changed
    }
}
