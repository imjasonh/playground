import Foundation

/// Bundled 11th Edition construction catalog (points, DP, join edges, keywords).
struct ArmyCatalog: Codable, Equatable, Sendable {
    var version: String
    var edition: String
    var source: CatalogSource
    var battleSizes: [BattleSizeDefinition]
    var factions: [FactionDefinition]
    var detachments: [DetachmentDefinition]
    var datasheets: [DatasheetDefinition]

    struct CatalogSource: Codable, Equatable, Sendable {
        var mfm: String
        var datasheetKeywords: String
        var mfmVersion: String?
        var mfmFirstSeen: String?
        var note: String?
    }

    func battleSize(id: String) -> BattleSizeDefinition? {
        battleSizes.first { $0.id == id }
    }

    func faction(id: String) -> FactionDefinition? {
        factions.first { $0.id == id }
    }

    func detachment(id: String) -> DetachmentDefinition? {
        detachments.first { $0.id == id }
    }

    func datasheet(id: String) -> DatasheetDefinition? {
        datasheets.first { $0.id == id }
    }

    func enhancement(id: String) -> (DetachmentDefinition, EnhancementDefinition)? {
        for detachment in detachments {
            if let enhancement = detachment.enhancements.first(where: { $0.id == id }) {
                return (detachment, enhancement)
            }
        }
        return nil
    }
}

struct BattleSizeDefinition: Codable, Equatable, Identifiable, Sendable {
    var id: String
    var name: String
    var pointsLimit: Int
    var detachmentPointsBudget: Int
    var enhancementPickLimit: Int
    var datasheetDuplicateLimit: Int
    var battlelineDuplicateLimit: Int
    var dedicatedTransportDuplicateLimit: Int
}

struct FactionDefinition: Codable, Equatable, Identifiable, Sendable {
    var id: String
    var name: String
    var keywords: [String]
}

struct DetachmentDefinition: Codable, Equatable, Identifiable, Sendable {
    var id: String
    var name: String
    var factionID: String
    var detachmentPoints: Int
    var forceDisposition: String
    var uniqueTag: String?
    var enhancements: [EnhancementDefinition]
}

struct EnhancementDefinition: Codable, Equatable, Identifiable, Sendable {
    var id: String
    var name: String
    var points: Int
    var isUpgrade: Bool
}

enum CatalogCharacterRole: String, Codable, Equatable, Sendable {
    case leader
    case character
}

struct DatasheetDefinition: Codable, Equatable, Identifiable, Sendable {
    var id: String
    var name: String
    var factionID: String
    var keywords: [String]
    var characterRole: CatalogCharacterRole?
    var epicHero: Bool
    var battleline: Bool
    var dedicatedTransport: Bool
    var minModels: Int
    var maxModels: Int
    var modelCounts: [Int]
    var pointsTiers: [PointsTier]
    var leaderTo: [String]
    var mustAttach: Bool
    var maxCopiesOverride: Int?

    struct PointsTier: Codable, Equatable, Sendable {
        /// 1-based copy index this tier starts at.
        var fromCopy: Int
        /// Inclusive end copy index, or `nil` for open-ended.
        var toCopy: Int?
        /// Points by model count string keys ("5", "10").
        var byModels: [String: Int]
    }

    func points(models: Int, copyIndex: Int) -> Int? {
        guard let tier = pointsTiers.first(where: { tier in
            if copyIndex < tier.fromCopy { return false }
            if let to = tier.toCopy, copyIndex > to { return false }
            return true
        }) else {
            return nil
        }
        return tier.byModels[String(models)]
    }
}
