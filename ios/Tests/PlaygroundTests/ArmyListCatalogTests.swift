import XCTest
@testable import Playground

final class ArmyListCatalogTests: XCTestCase {
    func testCatalogLoadsFromDisk() throws {
        let catalog = try Self.loadCatalogFromRepo()
        XCTAssertEqual(catalog.edition, "11th")
        XCTAssertFalse(catalog.version.isEmpty)
        XCTAssertEqual(catalog.factions.count, 1)
        XCTAssertEqual(catalog.factions[0].id, "leagues-of-votann")
        XCTAssertEqual(catalog.battleSizes.count, 2)
        XCTAssertGreaterThanOrEqual(catalog.detachments.count, 10)
        XCTAssertGreaterThanOrEqual(catalog.datasheets.count, 20)
    }

    func testHearthkynIsBattleline() throws {
        let catalog = try Self.loadCatalogFromRepo()
        let warriors = try XCTUnwrap(catalog.datasheet(id: "hearthkyn-warriors"))
        XCTAssertTrue(warriors.battleline)
        XCTAssertEqual(warriors.points(models: 10, copyIndex: 1), 90)
    }

    func testHearthbandUniqueTagAndDP() throws {
        let catalog = try Self.loadCatalogFromRepo()
        let hearthband = try XCTUnwrap(catalog.detachment(id: "hearthband"))
        XCTAssertEqual(hearthband.detachmentPoints, 3)
        XCTAssertEqual(hearthband.uniqueTag, "Hearthband")
        let covenant = try XCTUnwrap(catalog.detachment(id: "hearthguard-covenant"))
        XCTAssertEqual(covenant.uniqueTag, "Hearthband")
        XCTAssertEqual(covenant.detachmentPoints, 1)
    }

    func testPointsStepperForThunderkyn() throws {
        let catalog = try Self.loadCatalogFromRepo()
        let sheet = try XCTUnwrap(catalog.datasheet(id: "brokhyr-thunderkyn"))
        XCTAssertEqual(sheet.points(models: 6, copyIndex: 1), 170)
        XCTAssertEqual(sheet.points(models: 6, copyIndex: 2), 170)
        XCTAssertEqual(sheet.points(models: 6, copyIndex: 3), 180)
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
        var list = ArmyListDocument(
            name: "Empty",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion"
        )
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertFalse(result.isLegal)
        XCTAssertTrue(result.errors.contains { $0.code == "detachment.required" })
        _ = list
    }

    func testDPOverBudget() {
        var list = sampleLegalIncursion()
        // Hearthband is 3 DP; Incursion budget is 2.
        list.detachmentIDs = ["hearthband"]
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "dp.overBudget" })
    }

    func testUniqueTagCollision() {
        var list = sampleLegalIncursion()
        list.detachmentIDs = ["hearthband", "hearthguard-covenant"]
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
        let hekaton = try! XCTUnwrap(catalog.datasheet(id: "hekaton-land-fortress"))
        list.units.append(ListUnitInstance(datasheetID: hekaton.id, models: 1))
        list.units.append(ListUnitInstance(datasheetID: hekaton.id, models: 1))
        list.units.append(ListUnitInstance(datasheetID: hekaton.id, models: 1))
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "points.overLimit" })
    }

    func testBattlelineDuplicateCapIncursion() {
        var list = sampleLegalIncursion()
        list.units = (0..<5).map { _ in
            ListUnitInstance(datasheetID: "hearthkyn-warriors", models: 10)
        }
        // Keep a warlord character
        let kahl = ListUnitInstance(datasheetID: "kahl", models: 1)
        list.units.append(kahl)
        list.warlordUnitID = kahl.id
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "unit.duplicateCap" })
    }

    func testIllegalAttachment() {
        var list = sampleLegalIncursion()
        let warriors = ListUnitInstance(datasheetID: "hearthkyn-warriors", models: 10)
        let champion = ListUnitInstance(
            datasheetID: "einhyr-champion",
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
        let warriors = ListUnitInstance(datasheetID: "hearthkyn-warriors", models: 10)
        let kahl = ListUnitInstance(
            datasheetID: "kahl",
            models: 1,
            attachedToUnitID: warriors.id
        )
        list.units = [
            warriors,
            kahl,
            ListUnitInstance(datasheetID: "hearthkyn-warriors", models: 10),
            ListUnitInstance(datasheetID: "cthonian-beserks", models: 5),
            ListUnitInstance(datasheetID: "hernkyn-pioneers", models: 3),
            ListUnitInstance(datasheetID: "sagitaur", models: 1),
            ListUnitInstance(datasheetID: "hernkyn-yaegirs", models: 10),
        ]
        list.warlordUnitID = kahl.id
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertFalse(result.errors.contains { $0.code == "unit.attachIllegal" })
        XCTAssertTrue(result.isLegal, result.errors.map(\.message).joined(separator: "; "))
    }

    func testWarlordMustBeCharacter() {
        var list = sampleLegalIncursion()
        let warriors = list.units.first { $0.datasheetID == "hearthkyn-warriors" }!
        list.warlordUnitID = warriors.id
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "warlord.notCharacter" })
    }

    func testEnhancementRequiresDetachment() {
        var list = sampleLegalIncursion()
        guard let kahlIndex = list.units.firstIndex(where: { $0.datasheetID == "kahl" }) else {
            return XCTFail("missing kahl")
        }
        // High Kâhl is on Hearthband / Hearthguard Covenant — not on Brandfast.
        list.units[kahlIndex].enhancementIDs = ["hearthband--high-kahl"]
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "enhancement.detachmentNotSelected" })
    }

    func testEnhancementPickLimitIncursion() {
        var list = sampleLegalIncursion()
        // Brandfast has character enhancements. Add a second character with another enhancement.
        let grimnyr = ListUnitInstance(
            datasheetID: "grimnyr",
            models: 3,
            enhancementIDs: ["brandfast-oathband--signature-restoration"]
        )
        guard let kahlIndex = list.units.firstIndex(where: { $0.datasheetID == "kahl" }) else {
            return XCTFail("missing kahl")
        }
        list.units[kahlIndex].enhancementIDs = ["brandfast-oathband--precursive-judgement"]
        list.units.append(grimnyr)
        // Incursion allows 2 picks — still legal. Add a third.
        let ironMaster = ListUnitInstance(
            datasheetID: "brokhyr-iron-master",
            models: 5,
            enhancementIDs: ["brandfast-oathband--tactical-alchemy"]
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

    /// ~990 pt Brandfast Incursion list used as the golden legal sample.
    private func sampleLegalIncursion() -> ArmyListDocument {
        let kahl = ListUnitInstance(datasheetID: "kahl", models: 1)
        let warriorsA = ListUnitInstance(datasheetID: "hearthkyn-warriors", models: 10)
        let warriorsB = ListUnitInstance(datasheetID: "hearthkyn-warriors", models: 10)
        let beserks = ListUnitInstance(datasheetID: "cthonian-beserks", models: 5)
        let pioneers = ListUnitInstance(datasheetID: "hernkyn-pioneers", models: 3)
        let yaegirs = ListUnitInstance(datasheetID: "hernkyn-yaegirs", models: 10)
        let sagitaur = ListUnitInstance(datasheetID: "sagitaur", models: 1)
        let steeljacks = ListUnitInstance(datasheetID: "ironkin-steeljacks-with-melee-weapons", models: 3)
        // Points: 65+90+90+95+80+90+85+75 = 670 — under 1000, plenty of headroom.
        return ArmyListDocument(
            name: "Forge-tight 1k",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            detachmentIDs: ["brandfast-oathband"],
            units: [kahl, warriorsA, warriorsB, beserks, pioneers, yaegirs, sagitaur, steeljacks],
            warlordUnitID: kahl.id
        )
    }
}
