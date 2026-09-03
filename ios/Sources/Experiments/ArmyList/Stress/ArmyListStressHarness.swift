import Foundation

/// Builds ~50 army lists for stress coverage. Legality is decided only by
/// `ArmyListValidator`. This harness never reimplements construction rules.
enum ArmyListStressHarness {
    struct BuiltList: Equatable {
        var name: String
        var list: ArmyListDocument
        /// What the scenario intends; must match `ArmyListValidator` or the run fails.
        var expectLegal: Bool
        var notes: String
    }

    struct FixtureEnvelope: Codable, Equatable {
        var expectedLegal: Bool
        var notes: String
        var list: ArmyListDocument
    }

    struct ManifestEntry: Codable, Equatable {
        var file: String
        var expectedLegal: Bool
        var name: String
    }

    /// Deterministic LCG so fixture contents (including UUIDs) stay stable.
    struct SeededRNG {
        private var state: UInt64

        init(seed: Int) {
            state = UInt64(UInt(bitPattern: Int(seed))) &+ 0x9E37_79B9
            if state == 0 { state = 1 }
        }

        mutating func next() -> UInt64 {
            state = state &* 6364136223846793005 &+ 1
            return state
        }

        mutating func nextUUID() -> UUID {
            var bytes: uuid_t = (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            withUnsafeMutableBytes(of: &bytes) { raw in
                for i in 0..<16 {
                    raw[i] = UInt8(next() & 0xff)
                }
                // RFC 4122 version 4 / variant 1 bits.
                raw[6] = (raw[6] & 0x0f) | 0x40
                raw[8] = (raw[8] & 0x3f) | 0x80
            }
            return UUID(uuid: bytes)
        }

        mutating func shuffle<T>(_ items: inout [T]) {
            guard items.count > 1 else { return }
            for i in stride(from: items.count - 1, through: 1, by: -1) {
                let j = Int(next() % UInt64(i + 1))
                items.swapAt(i, j)
            }
        }
    }

    static func buildFifty(catalog: ArmyCatalog) -> [BuiltList] {
        var lists: [BuiltList] = []
        let factions = catalog.factions.sorted { $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending }
        var seed = 0

        for faction in factions {
            if let built = fillList(
                catalog: catalog,
                faction: faction,
                battleSizeID: "incursion",
                seed: seed,
                attach: true,
                withEnhancement: true,
                targetFill: 0.90
            ) {
                lists.append(built)
            }
            seed += 1
        }

        let strikeFactionIDs = [
            "space-marines",
            "astra-militarum",
            "aeldari",
            "necrons",
            "orks",
            "tyranids",
            "tau-empire",
            "adepta-sororitas",
            "death-guard",
            "thousand-sons",
            "world-eaters",
            "blood-angels",
            "dark-angels",
            "space-wolves",
            "genestealer-cults",
            "drukhari",
            "grey-knights",
        ]
        for factionID in strikeFactionIDs {
            guard let faction = factions.first(where: { $0.id == factionID }) else { continue }
            if let built = fillList(
                catalog: catalog,
                faction: faction,
                battleSizeID: "strike-force",
                seed: seed,
                attach: true,
                withEnhancement: true,
                targetFill: 0.93
            ) {
                lists.append(built)
            }
            seed += 1
        }

        lists.append(contentsOf: buildIllegalSamples(catalog: catalog))
        if lists.count > 50 {
            return Array(lists.prefix(50))
        }
        return lists
    }

    /// Validates every built list with the Swift validator. Returns mismatch messages.
    static func mismatches(in lists: [BuiltList], catalog: ArmyCatalog) -> [String] {
        var messages: [String] = []
        for built in lists {
            let result = ArmyListValidator.validate(list: built.list, catalog: catalog)
            if result.isLegal != built.expectLegal {
                let codes = result.errors.map(\.code).joined(separator: ",")
                messages.append(
                    "\(built.name): expectedLegal=\(built.expectLegal) gotLegal=\(result.isLegal) errors=\(codes)"
                )
            }
        }
        return messages
    }

    static func writeFixtures(
        _ lists: [BuiltList],
        to directory: URL
    ) throws {
        let fm = FileManager.default
        try fm.createDirectory(at: directory, withIntermediateDirectories: true)
        let existing = try fm.contentsOfDirectory(
            at: directory,
            includingPropertiesForKeys: nil,
            options: [.skipsHiddenFiles]
        )
        for url in existing where url.pathExtension == "json" {
            try fm.removeItem(at: url)
        }

        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        encoder.dateEncodingStrategy = .iso8601

        var manifest: [ManifestEntry] = []
        for (index, built) in lists.enumerated() {
            let n = index + 1
            let rawSlug = String(
                format: "%02d-%@-%@-%@",
                n,
                built.expectLegal ? "legal" : "illegal",
                built.list.factionID,
                built.list.battleSizeID
            )
            let slug = rawSlug.map { ch -> Character in
                if ch.isLetter || ch.isNumber || ch == "-" || ch == "_" { return ch }
                return "-"
            }
            let fileName = String(slug) + ".json"
            let envelope = FixtureEnvelope(
                expectedLegal: built.expectLegal,
                notes: built.notes,
                list: built.list
            )
            let data = try encoder.encode(envelope)
            var text = String(data: data, encoding: .utf8) ?? ""
            if !text.hasSuffix("\n") { text += "\n" }
            try text.write(to: directory.appendingPathComponent(fileName), atomically: true, encoding: .utf8)
            manifest.append(
                ManifestEntry(file: fileName, expectedLegal: built.expectLegal, name: built.name)
            )
        }
        let manifestData = try encoder.encode(manifest)
        var manifestText = String(data: manifestData, encoding: .utf8) ?? ""
        if !manifestText.hasSuffix("\n") { manifestText += "\n" }
        try manifestText.write(
            to: directory.appendingPathComponent("manifest.json"),
            atomically: true,
            encoding: .utf8
        )
    }

    // MARK: - Builders

    private static func fillList(
        catalog: ArmyCatalog,
        faction: FactionDefinition,
        battleSizeID: String,
        seed: Int,
        attach: Bool,
        withEnhancement: Bool,
        targetFill: Double
    ) -> BuiltList? {
        guard let battle = catalog.battleSize(id: battleSizeID) else { return nil }
        let factionSheets = catalog.datasheets.filter { $0.factionID == faction.id }
        let factionDets = catalog.detachments.filter { $0.factionID == faction.id }

        let fixedDate = Date(timeIntervalSince1970: 1_767_225_600) // 2026-01-01Z
        var rng = SeededRNG(seed: seed)

        if factionDets.isEmpty {
            return BuiltList(
                name: "\(faction.name) \(battle.name) (no detachments)",
                list: ArmyListDocument(
                    id: rng.nextUUID(),
                    name: "\(faction.name) (no detachments)",
                    catalogVersion: catalog.version,
                    factionID: faction.id,
                    battleSizeID: battleSizeID,
                    notes: "Catalog has no detachments for this faction.",
                    createdAt: fixedDate,
                    updatedAt: fixedDate
                ),
                expectLegal: false,
                notes: "expected illegal: no detachments in catalog"
            )
        }

        let combos = detachmentCombos(factionDets, budget: battle.detachmentPointsBudget)
        guard !combos.isEmpty else { return nil }
        let dets = combos[seed % combos.count]

        guard let warlordSheet = pickWarlord(factionSheets) else {
            return BuiltList(
                name: "\(faction.name) \(battle.name) (no characters)",
                list: ArmyListDocument(
                    id: rng.nextUUID(),
                    name: "\(faction.name) (no characters)",
                    catalogVersion: catalog.version,
                    factionID: faction.id,
                    battleSizeID: battleSizeID,
                    detachmentIDs: dets.map(\.id),
                    notes: "Catalog has no Character/Leader datasheets.",
                    createdAt: fixedDate,
                    updatedAt: fixedDate
                ),
                expectLegal: false,
                notes: "expected illegal: no characters to be warlord"
            )
        }

        var units: [ListUnitInstance] = []
        var copies: [String: Int] = [:]
        var points = 0
        let limit = battle.pointsLimit
        let target = Int(Double(limit) * targetFill)

        var warlord = ListUnitInstance(
            id: rng.nextUUID(),
            datasheetID: warlordSheet.id,
            models: warlordSheet.minModels
        )
        let wCost = warlordSheet.points(models: warlord.models, copyIndex: 1) ?? 0
        units.append(warlord)
        copies[warlordSheet.id, default: 0] += 1
        points += wCost

        if withEnhancement {
            var charEnh: [EnhancementDefinition] = []
            for det in dets {
                for enh in det.enhancements where !enh.isUpgrade {
                    charEnh.append(enh)
                }
            }
            if !charEnh.isEmpty {
                let enh = charEnh[seed % charEnh.count]
                if points + enh.points <= limit {
                    warlord.enhancementIDs = [enh.id]
                    units[0] = warlord
                    points += enh.points
                }
            }
        }

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
            let lim: Int
            if let override = sheet.maxCopiesOverride {
                lim = min(override, sizeLimit)
            } else {
                lim = sizeLimit
            }
            if nextCopy > lim { return nil }
            guard let cost = sheet.points(models: models, copyIndex: nextCopy) else { return nil }
            if points + cost > limit { return nil }
            return cost
        }

        let battleline = factionSheets.filter(\.battleline)
        var fillers = factionSheets.filter { $0.characterRole == nil && !$0.epicHero }
        fillers.sort {
            ($0.points(models: $0.minModels, copyIndex: 1) ?? 9999)
                < ($1.points(models: $1.minModels, copyIndex: 1) ?? 9999)
        }
        var pool = battleline + fillers
        rng.shuffle(&pool)

        var bodyForAttach: ListUnitInstance?
        for sheet in pool {
            if points >= target { break }
            var modelOpts = sheet.modelCounts
            if sheet.battleline {
                modelOpts.sort(by: >)
            }
            for models in modelOpts {
                guard let cost = canAdd(sheet: sheet, models: models) else { continue }
                let unit = ListUnitInstance(id: rng.nextUUID(), datasheetID: sheet.id, models: models)
                units.append(unit)
                copies[sheet.id, default: 0] += 1
                points += cost
                if bodyForAttach == nil, sheet.characterRole == nil {
                    bodyForAttach = unit
                }
                break
            }
        }

        if attach, let body = bodyForAttach, !warlordSheet.leaderTo.isEmpty {
            if warlordSheet.leaderTo.contains(body.datasheetID) {
                warlord.attachedToUnitID = body.id
                units[0] = warlord
            } else if let existing = units.first(where: {
                $0.id != warlord.id && warlordSheet.leaderTo.contains($0.datasheetID)
            }) {
                warlord.attachedToUnitID = existing.id
                units[0] = warlord
            } else {
                for targetID in warlordSheet.leaderTo {
                    guard let sheet = factionSheets.first(where: { $0.id == targetID }) else { continue }
                    guard let cost = canAdd(sheet: sheet, models: sheet.minModels) else { continue }
                    let bodyUnit = ListUnitInstance(
                        id: rng.nextUUID(),
                        datasheetID: sheet.id,
                        models: sheet.minModels
                    )
                    units.append(bodyUnit)
                    copies[sheet.id, default: 0] += 1
                    points += cost
                    warlord.attachedToUnitID = bodyUnit.id
                    units[0] = warlord
                    break
                }
            }
        }

        let cheap = fillers
            .filter { $0.id != warlordSheet.id }
            .sorted {
                ($0.points(models: $0.minModels, copyIndex: 1) ?? 9999)
                    < ($1.points(models: $1.minModels, copyIndex: 1) ?? 9999)
            }
        for sheet in cheap {
            if points >= target { break }
            guard let cost = canAdd(sheet: sheet, models: sheet.minModels) else { continue }
            units.append(
                ListUnitInstance(id: rng.nextUUID(), datasheetID: sheet.id, models: sheet.minModels)
            )
            copies[sheet.id, default: 0] += 1
            points += cost
        }

        // Name points from the validator so the label matches Swift totals.
        var list = ArmyListDocument(
            id: rng.nextUUID(),
            name: "\(faction.name) \(battle.name)",
            catalogVersion: catalog.version,
            factionID: faction.id,
            battleSizeID: battleSizeID,
            detachmentIDs: dets.map(\.id),
            units: units,
            warlordUnitID: warlord.id,
            notes: "stress seed=\(seed) attach=\(attach) enh=\(withEnhancement)",
            createdAt: fixedDate,
            updatedAt: fixedDate
        )
        let validated = ArmyListValidator.validate(list: list, catalog: catalog)
        list.name = "\(faction.name) \(battle.name) \(validated.totalPoints)pts"
        return BuiltList(
            name: list.name,
            list: list,
            expectLegal: true,
            notes: "auto-built"
        )
    }

    private static func buildIllegalSamples(catalog: ArmyCatalog) -> [BuiltList] {
        let fixedDate = Date(timeIntervalSince1970: 1_767_225_600)
        guard
            let warriors = catalog.datasheet(id: "leagues-of-votann--hearthkyn-warriors"),
            let kahl = catalog.datasheet(id: "leagues-of-votann--kahl"),
            let hearthband = catalog.detachment(id: "leagues-of-votann--hearthband"),
            let moe = catalog.datasheet(id: "chaos-space-marines--master-of-executions"),
            let legionaries = catalog.datasheet(id: "chaos-space-marines--legionaries"),
            let csmDet = catalog.detachments.first(where: {
                $0.factionID == "chaos-space-marines" && $0.detachmentPoints == 2
            })
        else {
            return []
        }

        var rng = SeededRNG(seed: 10_000)
        let w = ListUnitInstance(id: rng.nextUUID(), datasheetID: warriors.id, models: 10)
        let warlordNotCharacter = BuiltList(
            name: "illegal warlord not character",
            list: ArmyListDocument(
                id: rng.nextUUID(),
                name: "Illegal warlord",
                catalogVersion: catalog.version,
                factionID: "leagues-of-votann",
                battleSizeID: "incursion",
                detachmentIDs: ["leagues-of-votann--brandfast-oathband"],
                units: [w],
                warlordUnitID: w.id,
                createdAt: fixedDate,
                updatedAt: fixedDate
            ),
            expectLegal: false,
            notes: "warlord.notCharacter"
        )

        let k = ListUnitInstance(id: rng.nextUUID(), datasheetID: kahl.id, models: 1)
        let w2 = ListUnitInstance(id: rng.nextUUID(), datasheetID: warriors.id, models: 10)
        let dpOver = BuiltList(
            name: "illegal DP over budget",
            list: ArmyListDocument(
                id: rng.nextUUID(),
                name: "Illegal DP",
                catalogVersion: catalog.version,
                factionID: "leagues-of-votann",
                battleSizeID: "incursion",
                detachmentIDs: [hearthband.id],
                units: [k, w2],
                warlordUnitID: k.id,
                createdAt: fixedDate,
                updatedAt: fixedDate
            ),
            expectLegal: false,
            notes: "dp.overBudget"
        )

        let body = ListUnitInstance(id: rng.nextUUID(), datasheetID: legionaries.id, models: 10)
        let character = ListUnitInstance(
            id: rng.nextUUID(),
            datasheetID: moe.id,
            models: 1,
            attachedToUnitID: body.id
        )
        let emptyLeaderTo = BuiltList(
            name: "illegal attach with empty leaderTo",
            list: ArmyListDocument(
                id: rng.nextUUID(),
                name: "Illegal empty leaderTo attach",
                catalogVersion: catalog.version,
                factionID: "chaos-space-marines",
                battleSizeID: "incursion",
                detachmentIDs: [csmDet.id],
                units: [body, character],
                warlordUnitID: character.id,
                createdAt: fixedDate,
                updatedAt: fixedDate
            ),
            expectLegal: false,
            notes: "unit.attachNoTargets"
        )

        return [warlordNotCharacter, dpOver, emptyLeaderTo]
    }

    private static func detachmentCombos(
        _ factionDets: [DetachmentDefinition],
        budget: Int
    ) -> [[DetachmentDefinition]] {
        var exact: [[DetachmentDefinition]] = []
        var under: [[DetachmentDefinition]] = []
        let n = factionDets.count
        let maxK = min(4, n)
        guard maxK >= 1 else { return [] }

        func tagsCollide(_ combo: [DetachmentDefinition]) -> Bool {
            let tags = combo.compactMap(\.uniqueTag)
            return tags.count != Set(tags).count
        }

        for k in 1...maxK {
            for combo in combinations(factionDets, k: k) {
                if tagsCollide(combo) { continue }
                let spent = combo.reduce(0) { $0 + $1.detachmentPoints }
                if spent == budget {
                    exact.append(combo)
                } else if spent > 0 && spent <= budget {
                    under.append(combo)
                }
            }
        }
        under.sort {
            $0.reduce(0) { $0 + $1.detachmentPoints } > $1.reduce(0) { $0 + $1.detachmentPoints }
        }
        return exact + under
    }

    private static func combinations<T>(_ items: [T], k: Int) -> [[T]] {
        guard k > 0, k <= items.count else { return [] }
        var result: [[T]] = []
        var indices = Array(0..<k)
        while true {
            result.append(indices.map { items[$0] })
            var i = k - 1
            while i >= 0 && indices[i] == i + items.count - k {
                i -= 1
            }
            if i < 0 { break }
            indices[i] += 1
            for j in (i + 1)..<k {
                indices[j] = indices[j - 1] + 1
            }
        }
        return result
    }

    private static func pickWarlord(_ sheets: [DatasheetDefinition]) -> DatasheetDefinition? {
        let nonEpicLeaders = sheets.filter { $0.characterRole == .leader && !$0.epicHero }
            .sorted { ($0.points(models: $0.minModels, copyIndex: 1) ?? 9999) < ($1.points(models: $1.minModels, copyIndex: 1) ?? 9999) }
        if let first = nonEpicLeaders.first { return first }
        if let leader = sheets.first(where: { $0.characterRole == .leader }) { return leader }
        let nonEpicChars = sheets.filter { $0.characterRole == .character && !$0.epicHero }
            .sorted { ($0.points(models: $0.minModels, copyIndex: 1) ?? 9999) < ($1.points(models: $1.minModels, copyIndex: 1) ?? 9999) }
        if let first = nonEpicChars.first { return first }
        return sheets.first { $0.characterRole == .character }
    }
}
