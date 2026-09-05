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

/// One choosable loadout entry inside an ``OptionGroupDefinition``.
struct OptionDefinition: Codable, Equatable, Identifiable, Sendable {
    var id: String
    var name: String
    var points: Int
}

/// Exclusive or optional wargear group from BattleScribe (0 pts is common).
struct OptionGroupDefinition: Codable, Equatable, Identifiable, Sendable {
    var id: String
    var name: String
    var min: Int
    var max: Int
    var defaultOptionID: String?
    var options: [OptionDefinition]

    func option(id: String) -> OptionDefinition? {
        options.first { $0.id == id }
    }
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
    /// Curated theme tokens (e.g. "aspect", "kabal", "plague") folded in from
    /// `ios/scripts/theme-keywords.json` so natural-language themes match units
    /// whose BSData keywords miss the concept. Empty for most datasheets.
    var themeKeywords: [String]
    var characterRole: CatalogCharacterRole?
    var epicHero: Bool
    var battleline: Bool
    var dedicatedTransport: Bool
    /// True when the points source marks this datasheet as Legends.
    var legends: Bool
    var minModels: Int
    var maxModels: Int
    var modelCounts: [Int]
    var pointsTiers: [PointsTier]
    var leaderTo: [String]
    var mustAttach: Bool
    var maxCopiesOverride: Int?
    /// BattleScribe loadout choice groups (plasma gun, etc.), including 0-pt picks.
    var optionGroups: [OptionGroupDefinition]

    struct PointsTier: Codable, Equatable, Sendable {
        /// 1-based copy index this tier starts at.
        var fromCopy: Int
        /// Inclusive end copy index, or `nil` for open-ended.
        var toCopy: Int?
        /// Points by model count string keys ("5", "10").
        var byModels: [String: Int]
    }

    enum CodingKeys: String, CodingKey {
        case id, name, factionID, keywords, themeKeywords, characterRole, epicHero
        case battleline, dedicatedTransport, legends, minModels, maxModels
        case modelCounts, pointsTiers, leaderTo, mustAttach, maxCopiesOverride
        case optionGroups
    }

    init(
        id: String,
        name: String,
        factionID: String,
        keywords: [String],
        themeKeywords: [String] = [],
        characterRole: CatalogCharacterRole?,
        epicHero: Bool,
        battleline: Bool,
        dedicatedTransport: Bool,
        legends: Bool = false,
        minModels: Int,
        maxModels: Int,
        modelCounts: [Int],
        pointsTiers: [PointsTier],
        leaderTo: [String],
        mustAttach: Bool,
        maxCopiesOverride: Int?,
        optionGroups: [OptionGroupDefinition] = []
    ) {
        self.id = id
        self.name = name
        self.factionID = factionID
        self.keywords = keywords
        self.themeKeywords = themeKeywords
        self.characterRole = characterRole
        self.epicHero = epicHero
        self.battleline = battleline
        self.dedicatedTransport = dedicatedTransport
        self.legends = legends
        self.minModels = minModels
        self.maxModels = maxModels
        self.modelCounts = modelCounts
        self.pointsTiers = pointsTiers
        self.leaderTo = leaderTo
        self.mustAttach = mustAttach
        self.maxCopiesOverride = maxCopiesOverride
        self.optionGroups = optionGroups
    }

    init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        id = try container.decode(String.self, forKey: .id)
        name = try container.decode(String.self, forKey: .name)
        factionID = try container.decode(String.self, forKey: .factionID)
        keywords = try container.decode([String].self, forKey: .keywords)
        themeKeywords = try container.decodeIfPresent([String].self, forKey: .themeKeywords) ?? []
        characterRole = try container.decodeIfPresent(CatalogCharacterRole.self, forKey: .characterRole)
        epicHero = try container.decode(Bool.self, forKey: .epicHero)
        battleline = try container.decode(Bool.self, forKey: .battleline)
        dedicatedTransport = try container.decode(Bool.self, forKey: .dedicatedTransport)
        legends = try container.decodeIfPresent(Bool.self, forKey: .legends) ?? false
        minModels = try container.decode(Int.self, forKey: .minModels)
        maxModels = try container.decode(Int.self, forKey: .maxModels)
        modelCounts = try container.decode([Int].self, forKey: .modelCounts)
        pointsTiers = try container.decode([PointsTier].self, forKey: .pointsTiers)
        leaderTo = try container.decode([String].self, forKey: .leaderTo)
        mustAttach = try container.decode(Bool.self, forKey: .mustAttach)
        maxCopiesOverride = try container.decodeIfPresent(Int.self, forKey: .maxCopiesOverride)
        optionGroups = try container.decodeIfPresent([OptionGroupDefinition].self, forKey: .optionGroups) ?? []
    }

    func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(id, forKey: .id)
        try container.encode(name, forKey: .name)
        try container.encode(factionID, forKey: .factionID)
        try container.encode(keywords, forKey: .keywords)
        if !themeKeywords.isEmpty {
            try container.encode(themeKeywords, forKey: .themeKeywords)
        }
        try container.encodeIfPresent(characterRole, forKey: .characterRole)
        try container.encode(epicHero, forKey: .epicHero)
        try container.encode(battleline, forKey: .battleline)
        try container.encode(dedicatedTransport, forKey: .dedicatedTransport)
        try container.encode(legends, forKey: .legends)
        try container.encode(minModels, forKey: .minModels)
        try container.encode(maxModels, forKey: .maxModels)
        try container.encode(modelCounts, forKey: .modelCounts)
        try container.encode(pointsTiers, forKey: .pointsTiers)
        try container.encode(leaderTo, forKey: .leaderTo)
        try container.encode(mustAttach, forKey: .mustAttach)
        try container.encodeIfPresent(maxCopiesOverride, forKey: .maxCopiesOverride)
        try container.encode(optionGroups, forKey: .optionGroups)
    }

    /// Default loadout picks for a newly added unit instance.
    func defaultOptionIDs() -> [String] {
        optionGroups.compactMap(\.defaultOptionID)
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

    func optionPoints(selectedIDs: [String]) -> Int {
        let selected = Set(selectedIDs)
        return optionGroups
            .flatMap(\.options)
            .filter { selected.contains($0.id) }
            .reduce(0) { $0 + $1.points }
    }
}
