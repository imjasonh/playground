import XCTest
@testable import Playground

@MainActor
final class ArmyListChatToolTests: XCTestCase {
    private var catalog: ArmyCatalog!
    private var workspace: ArmyListChatWorkspace!

    override func setUpWithError() throws {
        catalog = try ArmyListCatalogTests.loadCatalogFromRepo()
        let list = ArmyListDocument(
            name: "Chat test",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion"
        )
        workspace = ArmyListChatWorkspace(list: list, catalog: catalog)
    }

    func testSearchCatalogFindsWarriors() {
        let result = ArmyListChatToolExecutor.searchCatalog(
            workspace: workspace,
            query: "hearthkyn",
            kind: "unit"
        )
        XCTAssertTrue(result.contains("hearthkyn-warriors"))
    }

    func testBuildLegalIncursionViaTools() {
        _ = ArmyListChatToolExecutor.setBattleSize(workspace: workspace, battleSizeID: "1000")
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.clearUnits(workspace: workspace)

        let adds: [(String, Double)] = [
            ("kahl", 1),
            ("hearthkyn-warriors", 10),
            ("hearthkyn-warriors", 10),
            ("cthonian-beserks", 5),
            ("hernkyn-pioneers", 3),
            ("hernkyn-yaegirs", 10),
            ("sagitaur", 1),
            ("ironkin-steeljacks-with-melee-weapons", 3),
        ]
        for (id, models) in adds {
            let output = ArmyListChatToolExecutor.addUnit(
                workspace: workspace,
                datasheetID: id,
                models: models
            )
            XCTAssertFalse(output.contains("Unknown datasheet"), output)
        }

        let kahl = try! XCTUnwrap(workspace.list.units.first { $0.datasheetID == "kahl" })
        _ = ArmyListChatToolExecutor.setWarlord(
            workspace: workspace,
            unitID: kahl.id.uuidString
        )
        _ = ArmyListChatToolExecutor.setListName(
            workspace: workspace,
            name: "Tool-built 1k"
        )

        let result = workspace.validation
        XCTAssertTrue(result.isLegal, result.errors.map(\.message).joined(separator: "; "))
        XCTAssertEqual(workspace.list.name, "Tool-built 1k")
        XCTAssertLessThanOrEqual(result.totalPoints, 1000)
    }

    func testIllegalDetachmentStillReported() {
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "hearthband"
        )
        let summary = ArmyListChatToolExecutor.getListSummary(workspace: workspace)
        XCTAssertTrue(summary.contains("ILLEGAL") || summary.contains("[ERROR]"))
        XCTAssertTrue(workspace.validation.errors.contains { $0.code == "dp.overBudget" })
    }

    func testAttachAndEnhancementTools() {
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "hearthkyn-warriors",
            models: 10
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "kahl",
            models: 1
        )
        let warriors = try! XCTUnwrap(workspace.list.units.first { $0.datasheetID == "hearthkyn-warriors" })
        let kahl = try! XCTUnwrap(workspace.list.units.first { $0.datasheetID == "kahl" })

        let attach = ArmyListChatToolExecutor.attachCharacter(
            workspace: workspace,
            characterUnitID: kahl.id.uuidString,
            bodyUnitID: warriors.id.uuidString
        )
        XCTAssertTrue(attach.contains("Attached") || attach.contains("LEGAL") || attach.contains("ILLEGAL"))

        let enhancement = ArmyListChatToolExecutor.setEnhancement(
            workspace: workspace,
            unitID: kahl.id.uuidString,
            enhancementID: "brandfast-oathband--precursive-judgement"
        )
        XCTAssertTrue(enhancement.contains("precursive-judgement") || enhancement.contains("Set enhancement"))
        XCTAssertEqual(workspace.list.units.first { $0.id == kahl.id }?.enhancementIDs.first, "brandfast-oathband--precursive-judgement")
    }

    func testRuntimeGateDoesNotCrash() {
        let runtime = ArmyListChatRuntime(workspace: workspace)
        runtime.refreshModelStatus()
        XCTAssertFalse(runtime.modelGate.title.isEmpty)
        XCTAssertFalse(runtime.armyListGateDetail.isEmpty)
    }
}
