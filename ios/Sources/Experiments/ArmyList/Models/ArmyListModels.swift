import Foundation

/// A saved army list document.
struct ArmyListDocument: Identifiable, Codable, Equatable, Sendable {
    var id: UUID
    var name: String
    var catalogVersion: String
    var factionID: String
    var battleSizeID: String
    var detachmentIDs: [String]
    var units: [ListUnitInstance]
    var warlordUnitID: UUID?
    var notes: String
    var createdAt: Date
    var updatedAt: Date

    init(
        id: UUID = UUID(),
        name: String,
        catalogVersion: String,
        factionID: String,
        battleSizeID: String,
        detachmentIDs: [String] = [],
        units: [ListUnitInstance] = [],
        warlordUnitID: UUID? = nil,
        notes: String = "",
        createdAt: Date = Date(),
        updatedAt: Date = Date()
    ) {
        self.id = id
        self.name = name
        self.catalogVersion = catalogVersion
        self.factionID = factionID
        self.battleSizeID = battleSizeID
        self.detachmentIDs = detachmentIDs
        self.units = units
        self.warlordUnitID = warlordUnitID
        self.notes = notes
        self.createdAt = createdAt
        self.updatedAt = updatedAt
    }

    mutating func touch() {
        updatedAt = Date()
    }
}

/// One unit entry on a list (a datasheet instance with options and attachments).
struct ListUnitInstance: Identifiable, Codable, Equatable, Sendable {
    var id: UUID
    var datasheetID: String
    var models: Int
    var optionIDs: [String]
    var enhancementIDs: [String]
    /// Bodyguard unit this Leader/Character is attached to.
    var attachedToUnitID: UUID?

    init(
        id: UUID = UUID(),
        datasheetID: String,
        models: Int,
        optionIDs: [String] = [],
        enhancementIDs: [String] = [],
        attachedToUnitID: UUID? = nil
    ) {
        self.id = id
        self.datasheetID = datasheetID
        self.models = models
        self.optionIDs = optionIDs
        self.enhancementIDs = enhancementIDs
        self.attachedToUnitID = attachedToUnitID
    }
}

enum ValidationSeverity: String, Codable, Equatable, Sendable {
    case error
    case warning
}

struct ValidationIssue: Identifiable, Equatable, Sendable {
    /// Stable machine code, e.g. `dp.overBudget`.
    var code: String
    var severity: ValidationSeverity
    var message: String
    var unitID: UUID?

    var id: String {
        if let unitID {
            return "\(code):\(unitID.uuidString)"
        }
        return code + ":" + message
    }
}

struct ValidationResult: Equatable, Sendable {
    var issues: [ValidationIssue]
    var totalPoints: Int
    var detachmentPointsSpent: Int

    var errors: [ValidationIssue] { issues.filter { $0.severity == .error } }
    var warnings: [ValidationIssue] { issues.filter { $0.severity == .warning } }
    var isLegal: Bool { errors.isEmpty }
}
