import Foundation

/// Bundled 11th Edition construction catalog (points, DP, join edges, keywords).
struct ArmyCatalog: Codable, Equatable, Sendable {
    var version: String
    var edition: String
    var source: CatalogSource
    /// Old id → new id for datasheets, detachments, and enhancements after a refresh.
    var idMigrations: [CatalogIDMigration]
    var battleSizes: [BattleSizeDefinition]
    var factions: [FactionDefinition]
    var detachments: [DetachmentDefinition]
    var datasheets: [DatasheetDefinition]

    struct CatalogSource: Codable, Equatable, Sendable {
        var pointsSource: String
        var datasheetKeywords: String
        var pointsRevision: String?
        var generatedAt: String?
        var note: String?

        enum CodingKeys: String, CodingKey {
            case pointsSource
            case datasheetKeywords
            case pointsRevision
            case generatedAt
            case note
            // Older bundled catalogs used these keys.
            case mfm
            case mfmVersion
            case mfmFirstSeen
        }

        init(
            pointsSource: String,
            datasheetKeywords: String,
            pointsRevision: String? = nil,
            generatedAt: String? = nil,
            note: String? = nil
        ) {
            self.pointsSource = pointsSource
            self.datasheetKeywords = datasheetKeywords
            self.pointsRevision = pointsRevision
            self.generatedAt = generatedAt
            self.note = note
        }

        init(from decoder: Decoder) throws {
            let container = try decoder.container(keyedBy: CodingKeys.self)
            pointsSource = try container.decodeIfPresent(String.self, forKey: .pointsSource)
                ?? container.decode(String.self, forKey: .mfm)
            datasheetKeywords = try container.decode(String.self, forKey: .datasheetKeywords)
            pointsRevision = try container.decodeIfPresent(String.self, forKey: .pointsRevision)
                ?? container.decodeIfPresent(String.self, forKey: .mfmVersion)
            generatedAt = try container.decodeIfPresent(String.self, forKey: .generatedAt)
                ?? container.decodeIfPresent(String.self, forKey: .mfmFirstSeen)
            note = try container.decodeIfPresent(String.self, forKey: .note)
        }

        func encode(to encoder: Encoder) throws {
            var container = encoder.container(keyedBy: CodingKeys.self)
            try container.encode(pointsSource, forKey: .pointsSource)
            try container.encode(datasheetKeywords, forKey: .datasheetKeywords)
            try container.encodeIfPresent(pointsRevision, forKey: .pointsRevision)
            try container.encodeIfPresent(generatedAt, forKey: .generatedAt)
            try container.encodeIfPresent(note, forKey: .note)
        }
    }

    enum CodingKeys: String, CodingKey {
        case version, edition, source, idMigrations
        case battleSizes, factions, detachments, datasheets
    }

    init(
        version: String,
        edition: String,
        source: CatalogSource,
        idMigrations: [CatalogIDMigration] = [],
        battleSizes: [BattleSizeDefinition],
        factions: [FactionDefinition],
        detachments: [DetachmentDefinition],
        datasheets: [DatasheetDefinition]
    ) {
        self.version = version
        self.edition = edition
        self.source = source
        self.idMigrations = idMigrations
        self.battleSizes = battleSizes
        self.factions = factions
        self.detachments = detachments
        self.datasheets = datasheets
    }

    init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        version = try container.decode(String.self, forKey: .version)
        edition = try container.decode(String.self, forKey: .edition)
        source = try container.decode(CatalogSource.self, forKey: .source)
        idMigrations = try container.decodeIfPresent([CatalogIDMigration].self, forKey: .idMigrations) ?? []
        battleSizes = try container.decode([BattleSizeDefinition].self, forKey: .battleSizes)
        factions = try container.decode([FactionDefinition].self, forKey: .factions)
        detachments = try container.decode([DetachmentDefinition].self, forKey: .detachments)
        datasheets = try container.decode([DatasheetDefinition].self, forKey: .datasheets)
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

    /// Resolves a chain of id migrations to the current catalog id.
    func migratedID(_ id: String) -> String {
        var current = id
        var seen = Set<String>()
        let byFrom = Dictionary(uniqueKeysWithValues: idMigrations.map { ($0.from, $0.to) })
        while let next = byFrom[current], !seen.contains(current) {
            seen.insert(current)
            current = next
        }
        return current
    }
}

/// Remaps an id stored on a saved list after a catalog refresh.
struct CatalogIDMigration: Codable, Equatable, Sendable {
    var from: String
    var to: String
    /// `datasheet`, `detachment`, or `enhancement`.
    var kind: String
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
