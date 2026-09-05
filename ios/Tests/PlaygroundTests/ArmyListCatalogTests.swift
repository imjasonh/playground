import XCTest
@testable import Playground

final class ArmyListCatalogTests: XCTestCase {
    func testCatalogLoadsFromDisk() throws {
        let catalog = try Self.loadCatalogFromRepo()
        XCTAssertEqual(catalog.edition, "11th")
        XCTAssertFalse(catalog.version.isEmpty)
        XCTAssertGreaterThanOrEqual(catalog.factions.count, 20)
        XCTAssertTrue(catalog.factions.contains { $0.id == "leagues-of-votann" })
        XCTAssertTrue(catalog.factions.contains { $0.id == "space-marines" })
        XCTAssertTrue(catalog.factions.contains { $0.id == "tyranids" })
        XCTAssertEqual(catalog.battleSizes.count, 2)
        XCTAssertGreaterThanOrEqual(catalog.detachments.count, 300)
        XCTAssertGreaterThanOrEqual(catalog.datasheets.count, 1500)
    }

    /// Hosted unit tests use Playground.app as Bundle.main. If catalog.json is
    /// not in Copy Bundle Resources, TestFlight shows "Catalog unavailable".
    func testCatalogLoadsFromAppBundle() throws {
        do {
            let catalog = try CatalogLoader.load(bundle: .main)
            XCTAssertFalse(catalog.factions.isEmpty)
            XCTAssertEqual(catalog.edition, "11th")
        } catch CatalogLoader.LoadError.missingResource {
            XCTFail(
                "catalog.json missing from app bundle. In project.yml, add it under sources with buildPhase: resources (XcodeGen has no target-level resources key)."
            )
        }
    }

    /// Regression for the TestFlight blank Create sheet: presentation cases
    /// carry the catalog (or error), never a second `@State`.
    func testHomePresentationCarriesCatalogOnCase() throws {
        let catalog = try CatalogLoader.load(bundle: .main)
        if case .create(let embedded) = ArmyListHomeView.Presentation.create(catalog) {
            XCTAssertEqual(embedded.version, catalog.version)
        } else {
            XCTFail("expected .create")
        }

        if case .unavailable(let message) = ArmyListHomeView.Presentation.unavailable("missing") {
            XCTAssertEqual(message, "missing")
        } else {
            XCTFail("expected .unavailable")
        }

        let list = ArmyListDocument(
            name: "Test",
            catalogVersion: catalog.version,
            factionID: catalog.factions[0].id,
            battleSizeID: catalog.battleSizes[0].id
        )
        if case .editor(let embeddedList, let embeddedCatalog) =
            ArmyListHomeView.Presentation.editor(list: list, catalog: catalog)
        {
            XCTAssertEqual(embeddedList.id, list.id)
            XCTAssertEqual(embeddedCatalog.version, catalog.version)
        } else {
            XCTFail("expected .editor")
        }
    }

    func testFactionScopedIdsDoNotCollide() throws {
        let catalog = try Self.loadCatalogFromRepo()
        let captainIDs = catalog.datasheets
            .filter { $0.name == "Captain" }
            .map(\.id)
        XCTAssertGreaterThanOrEqual(captainIDs.count, 2)
        XCTAssertEqual(Set(captainIDs).count, captainIDs.count)
        XCTAssertTrue(captainIDs.allSatisfy { $0.contains("--") })
    }

    func testHearthkynIsBattleline() throws {
        let catalog = try Self.loadCatalogFromRepo()
        let warriors = try XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--hearthkyn-warriors"))
        XCTAssertTrue(warriors.battleline)
        XCTAssertEqual(warriors.points(models: 10, copyIndex: 1), 90)
    }

    func testHearthbandUniqueTagAndDP() throws {
        let catalog = try Self.loadCatalogFromRepo()
        let hearthband = try XCTUnwrap(catalog.detachment(id: "leagues-of-votann--hearthband"))
        XCTAssertEqual(hearthband.detachmentPoints, 3)
        XCTAssertEqual(hearthband.uniqueTag, "Hearthband")
        let covenant = try XCTUnwrap(catalog.detachment(id: "leagues-of-votann--hearthguard-covenant"))
        XCTAssertEqual(covenant.uniqueTag, "Hearthband")
        XCTAssertEqual(covenant.detachmentPoints, 1)
    }

    func testPointsStepperForThunderkyn() throws {
        let catalog = try Self.loadCatalogFromRepo()
        let sheet = try XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--brokhyr-thunderkyn"))
        XCTAssertEqual(sheet.points(models: 6, copyIndex: 1), 170)
        XCTAssertEqual(sheet.points(models: 6, copyIndex: 2), 170)
        XCTAssertEqual(sheet.points(models: 6, copyIndex: 3), 180)
    }

    func testCatalogVersionHasNoMFMToken() throws {
        let catalog = try Self.loadCatalogFromRepo()
        XCTAssertFalse(catalog.version.localizedCaseInsensitiveContains("mfm"))
        XCTAssertTrue(catalog.version.hasPrefix("11e-"))
        XCTAssertFalse(catalog.source.pointsSource.isEmpty)
    }

    func testIDMigrationRemapsSavedListAndBumpsVersion() throws {
        var catalog = try Self.loadCatalogFromRepo()
        catalog.idMigrations = [
            CatalogIDMigration(
                from: "legacy--hearthkyn",
                to: "leagues-of-votann--hearthkyn-warriors",
                kind: "datasheet"
            ),
            CatalogIDMigration(
                from: "legacy--hearthband",
                to: "leagues-of-votann--hearthband",
                kind: "detachment"
            ),
        ]
        catalog.version = "11e-999"

        let warriors = try XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--hearthkyn-warriors"))
        let khal = try XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--kahl"))
        let body = ListUnitInstance(datasheetID: "legacy--hearthkyn", models: warriors.minModels)
        let leader = ListUnitInstance(
            datasheetID: khal.id,
            models: 1,
            attachedToUnitID: body.id
        )
        var list = ArmyListDocument(
            name: "Migrate me",
            catalogVersion: "11e-0",
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            detachmentIDs: ["legacy--hearthband"],
            units: [body, leader],
            warlordUnitID: leader.id
        )

        XCTAssertTrue(list.applyCatalogUpgrade(using: catalog))
        XCTAssertEqual(list.detachmentIDs, ["leagues-of-votann--hearthband"])
        XCTAssertEqual(list.units[0].datasheetID, "leagues-of-votann--hearthkyn-warriors")
        XCTAssertEqual(list.catalogVersion, "11e-999")
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertFalse(result.errors.contains { $0.code == "unit.unknownDatasheet" })
        XCTAssertFalse(result.errors.contains { $0.code == "detachment.unknown" })
    }

    static func loadCatalogFromRepo() throws -> ArmyCatalog {
        let thisFile = URL(fileURLWithPath: #filePath)
        // ios/Tests/PlaygroundTests/ArmyListCatalogTests.swift -> ios/
        let iosRoot = thisFile
            .deletingLastPathComponent() // PlaygroundTests
            .deletingLastPathComponent() // Tests
            .deletingLastPathComponent() // ios
        let url = iosRoot
            .appendingPathComponent("Sources/Experiments/ArmyList/Catalog/Resources/catalog.json")
        return try CatalogLoader.load(from: url)
    }
}

final class ArmyListValidatorTests: XCTestCase {
    private var catalog: ArmyCatalog!

    override func setUpWithError() throws {
        catalog = try ArmyListCatalogTests.loadCatalogFromRepo()
    }

    func testEmptyListIsIllegalWithoutDetachment() {
        let list = ArmyListDocument(
            name: "Empty",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion"
        )
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertFalse(result.isLegal)
        XCTAssertTrue(result.errors.contains { $0.code == "detachment.required" })
    }

    func testDPOverBudget() {
        var list = sampleLegalIncursion()
        // Hearthband is 3 DP; Incursion budget is 2.
        list.detachmentIDs = ["leagues-of-votann--hearthband"]
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "dp.overBudget" })
    }

    func testUniqueTagCollision() {
        var list = sampleLegalIncursion()
        list.detachmentIDs = ["leagues-of-votann--hearthband", "leagues-of-votann--hearthguard-covenant"]
        list.battleSizeID = "strike-force"
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "detachment.uniqueTagCollision" })
    }

    func testLegalIncursionSample() {
        let list = sampleLegalIncursion()
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.isLegal, result.errors.map(\.message).joined(separator: "; "))
        XCTAssertEqual(result.detachmentPointsSpent, 2)
        XCTAssertLessThanOrEqual(result.totalPoints, 1000)
        XCTAssertGreaterThan(result.totalPoints, 0)
    }

    func testPointsOverLimit() {
        var list = sampleLegalIncursion()
        // Stack expensive units past 1000.
        let hekaton = try! XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--hekaton-land-fortress"))
        list.units.append(ListUnitInstance(datasheetID: hekaton.id, models: 1))
        list.units.append(ListUnitInstance(datasheetID: hekaton.id, models: 1))
        list.units.append(ListUnitInstance(datasheetID: hekaton.id, models: 1))
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "points.overLimit" })
    }

    func testBattlelineDuplicateCapIncursion() {
        var list = sampleLegalIncursion()
        list.units = (0..<5).map { _ in
            ListUnitInstance(datasheetID: "leagues-of-votann--hearthkyn-warriors", models: 10)
        }
        // Keep a warlord character
        let kahl = ListUnitInstance(datasheetID: "leagues-of-votann--kahl", models: 1)
        list.units.append(kahl)
        list.warlordUnitID = kahl.id
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "unit.duplicateCap" })
    }

    func testIllegalAttachment() {
        var list = sampleLegalIncursion()
        let warriors = ListUnitInstance(datasheetID: "leagues-of-votann--hearthkyn-warriors", models: 10)
        let champion = ListUnitInstance(
            datasheetID: "leagues-of-votann--einhyr-champion",
            models: 1,
            attachedToUnitID: warriors.id
        )
        list.units = [warriors, champion]
        list.warlordUnitID = champion.id
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "unit.attachIllegal" })
    }

    func testLegalAttachment() {
        var list = sampleLegalIncursion()
        let warriors = ListUnitInstance(datasheetID: "leagues-of-votann--hearthkyn-warriors", models: 10)
        let kahl = ListUnitInstance(
            datasheetID: "leagues-of-votann--kahl",
            models: 1,
            attachedToUnitID: warriors.id
        )
        list.units = [
            warriors,
            kahl,
            ListUnitInstance(datasheetID: "leagues-of-votann--hearthkyn-warriors", models: 10),
            ListUnitInstance(datasheetID: "leagues-of-votann--cthonian-beserks", models: 5),
            ListUnitInstance(datasheetID: "leagues-of-votann--hernkyn-pioneers", models: 3),
            ListUnitInstance(datasheetID: "leagues-of-votann--sagitaur", models: 1),
            ListUnitInstance(datasheetID: "leagues-of-votann--hernkyn-yaegirs", models: 10),
        ]
        list.warlordUnitID = kahl.id
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertFalse(result.errors.contains { $0.code == "unit.attachIllegal" })
        XCTAssertTrue(result.isLegal, result.errors.map(\.message).joined(separator: "; "))
    }

    func testWarlordMustBeCharacter() {
        var list = sampleLegalIncursion()
        let warriors = list.units.first { $0.datasheetID == "leagues-of-votann--hearthkyn-warriors" }!
        list.warlordUnitID = warriors.id
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "warlord.notCharacter" })
    }

    func testEnhancementRequiresDetachment() {
        var list = sampleLegalIncursion()
        guard let kahlIndex = list.units.firstIndex(where: { $0.datasheetID == "leagues-of-votann--kahl" }) else {
            return XCTFail("missing kahl")
        }
        // High Kâhl is on Hearthband / Hearthguard Covenant — not on Brandfast.
        list.units[kahlIndex].enhancementIDs = ["leagues-of-votann--hearthband--high-kahl"]
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "enhancement.detachmentNotSelected" })
    }

    func testEnhancementPickLimitIncursion() {
        var list = sampleLegalIncursion()
        // Brandfast has character enhancements. Add a second character with another enhancement.
        let grimnyr = ListUnitInstance(
            datasheetID: "leagues-of-votann--grimnyr",
            models: 3,
            enhancementIDs: ["leagues-of-votann--brandfast-oathband--signature-restoration"]
        )
        guard let kahlIndex = list.units.firstIndex(where: { $0.datasheetID == "leagues-of-votann--kahl" }) else {
            return XCTFail("missing kahl")
        }
        list.units[kahlIndex].enhancementIDs = ["leagues-of-votann--brandfast-oathband--precursive-judgement"]
        list.units.append(grimnyr)
        // Incursion allows 2 picks — still legal. Add a third.
        let ironMaster = ListUnitInstance(
            datasheetID: "leagues-of-votann--brokhyr-iron-master",
            models: 5,
            enhancementIDs: ["leagues-of-votann--brandfast-oathband--tactical-alchemy"]
        )
        list.units.append(ironMaster)
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "enhancement.pickLimit" })
    }

    func testStoreRoundTrip() throws {
        let dir = FileManager.default.temporaryDirectory
            .appendingPathComponent("army-list-tests-\(UUID().uuidString)", isDirectory: true)
        let store = ArmyListStore(directory: dir)
        let list = sampleLegalIncursion()
        try store.save(list)
        let loaded = store.loadAll()
        XCTAssertEqual(loaded.count, 1)
        XCTAssertEqual(loaded[0].id, list.id)
        XCTAssertEqual(loaded[0].name, list.name)
        try store.delete(list)
        XCTAssertTrue(store.loadAll().isEmpty)
        try? FileManager.default.removeItem(at: dir)
    }

    func testJSONExportRoundTrip() throws {
        let list = sampleLegalIncursion()
        let validation = ArmyListValidator.validate(list: list, catalog: catalog)
        let data = try ArmyListJSONExporter.data(for: list, validation: validation)
        let imported = try ArmyListJSONExporter.document(from: data)
        XCTAssertEqual(imported.name, list.name)
        XCTAssertEqual(imported.factionID, list.factionID)
        XCTAssertEqual(imported.detachmentIDs, list.detachmentIDs)
        XCTAssertEqual(imported.units.count, list.units.count)
        let text = ArmyListTextExporter.text(for: list, catalog: catalog, validation: validation)
        XCTAssertTrue(text.contains(list.name))
        XCTAssertTrue(text.contains("LEGAL") || text.contains("ILLEGAL"))
        XCTAssertTrue(text.contains("Total:"))
    }

    func testLegendsFlagOnCatalogDatasheets() throws {
        let catalog = try CatalogLoader.load(bundle: .main)
        let aquila = try XCTUnwrap(catalog.datasheet(id: "astra-militarum--aquila-lander"))
        XCTAssertTrue(aquila.legends)
        let shock = try XCTUnwrap(catalog.datasheet(id: "astra-militarum--cadian-shock-troops"))
        XCTAssertFalse(shock.legends)
        XCTAssertGreaterThan(
            catalog.datasheets.filter(\.legends).count,
            100
        )
    }

    func testUnitPickerHidesLegendsByDefault() throws {
        let catalog = try CatalogLoader.load(bundle: .main)
        let withoutLegends = ArmyListUnitPickerFiltering.sheets(
            from: catalog,
            factionID: "astra-militarum",
            query: "",
            includeLegends: false,
            typeFilter: .all
        )
        XCTAssertFalse(withoutLegends.contains { $0.id == "astra-militarum--aquila-lander" })
        XCTAssertTrue(withoutLegends.contains { $0.id == "astra-militarum--cadian-shock-troops" })

        let withLegends = ArmyListUnitPickerFiltering.sheets(
            from: catalog,
            factionID: "astra-militarum",
            query: "",
            includeLegends: true,
            typeFilter: .all
        )
        XCTAssertTrue(withLegends.contains { $0.id == "astra-militarum--aquila-lander" })

        let battleline = ArmyListUnitPickerFiltering.sheets(
            from: catalog,
            factionID: "astra-militarum",
            query: "",
            includeLegends: false,
            typeFilter: .battleline
        )
        XCTAssertTrue(battleline.allSatisfy(\.battleline))
        XCTAssertFalse(battleline.contains { $0.legends })
    }

    func testCadianCommandSquadHasPlasmaLoadoutOptions() throws {
        let catalog = try CatalogLoader.load(bundle: .main)
        let sheet = try XCTUnwrap(catalog.datasheet(id: "astra-militarum--cadian-command-squad"))
        XCTAssertFalse(sheet.optionGroups.isEmpty)
        let optionNames = sheet.optionGroups.flatMap { $0.options.map(\.name) }
        XCTAssertTrue(optionNames.contains("Plasma gun"))
        XCTAssertTrue(optionNames.contains("Plasma gun and close combat weapon"))

        let defaults = sheet.defaultOptionIDs()
        XCTAssertEqual(defaults.count, sheet.optionGroups.filter { $0.min >= 1 }.count)

        var unit = ListUnitInstance(
            datasheetID: sheet.id,
            models: sheet.minModels,
            optionIDs: defaults
        )
        // Swap the standard-bearer slot to Plasma gun.
        let wargear = try XCTUnwrap(
            sheet.optionGroups.first { $0.name.contains("Wargear Options") }
        )
        let plasma = try XCTUnwrap(wargear.options.first { $0.name == "Plasma gun" })
        let groupIDs = Set(wargear.options.map(\.id))
        unit.optionIDs.removeAll { groupIDs.contains($0) }
        unit.optionIDs.append(plasma.id)
        XCTAssertEqual(sheet.optionPoints(selectedIDs: unit.optionIDs), 0)

        let list = ArmyListDocument(
            name: "CCS loadout",
            catalogVersion: catalog.version,
            factionID: "astra-militarum",
            battleSizeID: "incursion",
            units: [unit]
        )
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertFalse(result.errors.contains { $0.code == "option.groupCount" })
    }

    func testDuplicateUnitClearsAttachmentAndInsertsAfterSource() {
        let body = ListUnitInstance(datasheetID: "leagues-of-votann--hearthkyn-warriors", models: 10)
        var leader = ListUnitInstance(datasheetID: "leagues-of-votann--kahl", models: 1)
        leader.attachedToUnitID = body.id
        leader.enhancementIDs = ["detachment--example-enhancement"]
        var list = ArmyListDocument(
            name: "Dup",
            catalogVersion: "test",
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            units: [body, leader]
        )

        let newID = list.duplicateUnit(id: leader.id)
        XCTAssertEqual(list.units.count, 3)
        XCTAssertEqual(list.units[0].id, body.id)
        XCTAssertEqual(list.units[1].id, leader.id)
        let copy = list.units[2]
        XCTAssertEqual(copy.id, newID)
        XCTAssertEqual(copy.datasheetID, leader.datasheetID)
        XCTAssertEqual(copy.models, leader.models)
        XCTAssertEqual(copy.enhancementIDs, leader.enhancementIDs)
        XCTAssertNil(copy.attachedToUnitID)
        XCTAssertNotEqual(copy.id, leader.id)
    }

    func testMoveUnitsReordersRows() {
        let first = ListUnitInstance(datasheetID: "leagues-of-votann--kahl", models: 1)
        let second = ListUnitInstance(datasheetID: "leagues-of-votann--hearthkyn-warriors", models: 10)
        let third = ListUnitInstance(datasheetID: "leagues-of-votann--sagitaur", models: 1)
        var list = ArmyListDocument(
            name: "Reorder",
            catalogVersion: "test",
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            units: [first, second, third]
        )
        let before = list.updatedAt
        list.moveUnits(fromOffsets: IndexSet(integer: 0), toOffset: 3)
        XCTAssertEqual(list.units.map(\.id), [second.id, third.id, first.id])
        XCTAssertGreaterThanOrEqual(list.updatedAt, before)
    }

    /// ~990 pt Brandfast Incursion list used as the golden legal sample.
    private func sampleLegalIncursion() -> ArmyListDocument {
        let kahl = ListUnitInstance(datasheetID: "leagues-of-votann--kahl", models: 1)
        let warriorsA = ListUnitInstance(datasheetID: "leagues-of-votann--hearthkyn-warriors", models: 10)
        let warriorsB = ListUnitInstance(datasheetID: "leagues-of-votann--hearthkyn-warriors", models: 10)
        let beserks = ListUnitInstance(datasheetID: "leagues-of-votann--cthonian-beserks", models: 5)
        let pioneers = ListUnitInstance(datasheetID: "leagues-of-votann--hernkyn-pioneers", models: 3)
        let yaegirs = ListUnitInstance(datasheetID: "leagues-of-votann--hernkyn-yaegirs", models: 10)
        let sagitaur = ListUnitInstance(datasheetID: "leagues-of-votann--sagitaur", models: 1)
        let steeljacks = ListUnitInstance(datasheetID: "leagues-of-votann--ironkin-steeljacks-with-melee-weapons", models: 3)
        // Points: 65+90+90+95+80+90+85+75 = 670 — under 1000, plenty of headroom.
        return ArmyListDocument(
            name: "Forge-tight 1k",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            detachmentIDs: ["leagues-of-votann--brandfast-oathband"],
            units: [kahl, warriorsA, warriorsB, beserks, pioneers, yaegirs, sagitaur, steeljacks],
            warlordUnitID: kahl.id
        )
    }
}
