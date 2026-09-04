import Foundation
import UniformTypeIdentifiers

/// Canonical `.army.json` export / import for Army List documents.
enum ArmyListJSONExporter {
    static let formatName = "playground.armyList"
    static let formatVersion = 1
    static let contentType = UTType(filenameExtension: "army.json") ?? .json

    struct Envelope: Codable, Equatable {
        var format: String
        var formatVersion: Int
        var catalogVersion: String
        var name: String
        var factionID: String
        var battleSizeID: String
        var detachmentIDs: [String]
        var units: [ListUnitInstance]
        var warlordUnitID: UUID?
        var notes: String
        var validation: ValidationStamp?

        struct ValidationStamp: Codable, Equatable {
            var errorCount: Int
            var warningCount: Int
            var totalPoints: Int
            var detachmentPointsSpent: Int
        }
    }

    static func envelope(
        for list: ArmyListDocument,
        validation: ValidationResult? = nil
    ) -> Envelope {
        Envelope(
            format: formatName,
            formatVersion: formatVersion,
            catalogVersion: list.catalogVersion,
            name: list.name,
            factionID: list.factionID,
            battleSizeID: list.battleSizeID,
            detachmentIDs: list.detachmentIDs,
            units: list.units,
            warlordUnitID: list.warlordUnitID,
            notes: list.notes,
            validation: validation.map {
                .init(
                    errorCount: $0.errors.count,
                    warningCount: $0.warnings.count,
                    totalPoints: $0.totalPoints,
                    detachmentPointsSpent: $0.detachmentPointsSpent
                )
            }
        )
    }

    static func data(for list: ArmyListDocument, validation: ValidationResult? = nil) throws -> Data {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        encoder.dateEncodingStrategy = .iso8601
        return try encoder.encode(envelope(for: list, validation: validation))
    }

    static func filename(for list: ArmyListDocument) -> String {
        let slug = list.name
            .lowercased()
            .replacingOccurrences(of: " ", with: "-")
            .filter { $0.isLetter || $0.isNumber || $0 == "-" }
        let base = slug.isEmpty ? "army-list" : slug
        return "\(base).army.json"
    }

    static func document(from data: Data) throws -> ArmyListDocument {
        let decoder = JSONDecoder()
        decoder.dateDecodingStrategy = .iso8601
        let envelope = try decoder.decode(Envelope.self, from: data)
        guard envelope.format == formatName else {
            throw ExportError.unsupportedFormat(envelope.format)
        }
        return ArmyListDocument(
            name: envelope.name,
            catalogVersion: envelope.catalogVersion,
            factionID: envelope.factionID,
            battleSizeID: envelope.battleSizeID,
            detachmentIDs: envelope.detachmentIDs,
            units: envelope.units,
            warlordUnitID: envelope.warlordUnitID,
            notes: envelope.notes
        )
    }

    enum ExportError: Error, Equatable, LocalizedError {
        case unsupportedFormat(String)

        var errorDescription: String? {
            switch self {
            case .unsupportedFormat(let format):
                return "Unsupported army list format “\(format)”."
            }
        }
    }
}

/// Human-readable roster text for paste / share.
enum ArmyListTextExporter {
    static func text(
        for list: ArmyListDocument,
        catalog: ArmyCatalog,
        validation: ValidationResult
    ) -> String {
        let faction = catalog.faction(id: list.factionID)?.name ?? list.factionID
        let battle = catalog.battleSize(id: list.battleSizeID)
        let battleName = battle.map { "\($0.name) \($0.pointsLimit)" } ?? list.battleSizeID
        let dpBudget = battle?.detachmentPointsBudget ?? 0

        var lines: [String] = []
        lines.append("\(list.name) / \(faction) / \(battleName)")
        let detachmentNames = list.detachmentIDs.compactMap { catalog.detachment(id: $0)?.name }
        lines.append(
            "Detachments: \(detachmentNames.joined(separator: ", ")) (DP \(validation.detachmentPointsSpent)/\(dpBudget))"
        )
        if let warlordID = list.warlordUnitID,
           let unit = list.units.first(where: { $0.id == warlordID }),
           let sheet = catalog.datasheet(id: unit.datasheetID)
        {
            lines.append("Warlord: \(sheet.name)")
        }
        lines.append("")
        for unit in list.units {
            let sheet = catalog.datasheet(id: unit.datasheetID)
            let name = sheet?.name ?? unit.datasheetID
            var detail = "- \(name) ×\(unit.models)"
            if let sheet {
                let copyIndex = list.units
                    .prefix(while: { $0.id != unit.id })
                    .filter { $0.datasheetID == unit.datasheetID }
                    .count + 1
                if let pts = sheet.points(models: unit.models, copyIndex: copyIndex) {
                    var unitPts = pts + sheet.optionPoints(selectedIDs: unit.optionIDs)
                    for optionID in unit.optionIDs {
                        if let option = sheet.optionGroups.flatMap(\.options).first(where: { $0.id == optionID }) {
                            detail += ", \(option.name)"
                        }
                    }
                    for enhancementID in unit.enhancementIDs {
                        if let (_, enhancement) = catalog.enhancement(id: enhancementID) {
                            unitPts += enhancement.points
                            detail += ", \(enhancement.name)"
                        }
                    }
                    detail += " (\(unitPts) pts)"
                }
            }
            if let bodyID = unit.attachedToUnitID,
               let body = list.units.first(where: { $0.id == bodyID }),
               let bodySheet = catalog.datasheet(id: body.datasheetID)
            {
                detail += " [joined to \(bodySheet.name)]"
            }
            lines.append(detail)
        }
        lines.append("")
        let status: String
        if validation.isLegal {
            status = validation.warnings.isEmpty
                ? "LEGAL"
                : "LEGAL (\(validation.warnings.count) warning\(validation.warnings.count == 1 ? "" : "s"))"
        } else {
            status = "ILLEGAL (\(validation.errors.count) error\(validation.errors.count == 1 ? "" : "s"))"
        }
        let limit = battle?.pointsLimit ?? 0
        lines.append("Total: \(validation.totalPoints)/\(limit)")
        lines.append("Status: \(status)")
        if !validation.issues.isEmpty {
            lines.append("")
            for issue in validation.issues {
                let mark = issue.severity == .error ? "ERROR" : "WARN"
                lines.append("[\(mark)] \(issue.message)")
            }
        }
        return lines.joined(separator: "\n")
    }
}
