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
        XCTAssertTrue(result.contains("leagues-of-votann--hearthkyn-warriors"))
    }

    func testBuildLegalIncursionViaTools() {
        _ = ArmyListChatToolExecutor.setBattleSize(workspace: workspace, battleSizeID: "1000")
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "leagues-of-votann--brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.clearUnits(workspace: workspace)

        let adds: [(String, Double)] = [
            ("leagues-of-votann--kahl", 1),
            ("leagues-of-votann--hearthkyn-warriors", 10),
            ("leagues-of-votann--hearthkyn-warriors", 10),
            ("leagues-of-votann--cthonian-beserks", 5),
            ("leagues-of-votann--hernkyn-pioneers", 3),
            ("leagues-of-votann--hernkyn-yaegirs", 10),
            ("leagues-of-votann--sagitaur", 1),
            ("leagues-of-votann--ironkin-steeljacks-with-melee-weapons", 3),
        ]
        for (id, models) in adds {
            let output = ArmyListChatToolExecutor.addUnit(
                workspace: workspace,
                datasheetID: id,
                models: models
            )
            XCTAssertFalse(output.contains("Unknown datasheet"), output)
        }

        let kahl = try! XCTUnwrap(workspace.list.units.first { $0.datasheetID == "leagues-of-votann--kahl" })
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
            detachmentIDsCSV: "leagues-of-votann--hearthband"
        )
        let summary = ArmyListChatToolExecutor.getListSummary(workspace: workspace)
        XCTAssertTrue(summary.contains("ILLEGAL") || summary.contains("[ERROR]"))
        XCTAssertTrue(workspace.validation.errors.contains { $0.code == "dp.overBudget" })
    }

    func testSeedLegalListBuildsIncursion() {
        let output = ArmyListChatToolExecutor.seedLegalList(
            workspace: workspace,
            battleSizeID: "incursion",
            name: "Seeded Votann"
        )
        XCTAssertTrue(output.contains("Status: LEGAL") || output.contains("Status: ILLEGAL"), output)
        XCTAssertEqual(workspace.list.name, "Seeded Votann")
        XCTAssertEqual(workspace.list.battleSizeID, "incursion")
        XCTAssertFalse(workspace.list.units.isEmpty)
        XCTAssertFalse(workspace.list.detachmentIDs.isEmpty)
        let result = workspace.validation
        XCTAssertTrue(
            result.isLegal,
            result.errors.map(\.message).joined(separator: "; ")
        )
        XCTAssertLessThanOrEqual(result.totalPoints, 1000)
    }

    func testContextWindowDetectionTreatsGenerationErrorMinusOne() {
        let err = NSError(
            domain: "FoundationModels.LanguageModelSession.GenerationError",
            code: -1,
            userInfo: [
                NSLocalizedDescriptionKey:
                    "The operation couldn’t be completed. (FoundationModels.LanguageModelSession.GenerationError error -1.)",
            ]
        )
        XCTAssertTrue(ArmyListChatRuntime.isExceededContextWindow(err))
        XCTAssertTrue(AgentRuntime.isExceededContextWindow(err))
    }

    func testMarkdownRendersBoldAndLists() {
        let attributed = ArmyListChatMarkdown.attributed("**Bold** and\n- one\n- two")
        let plain = String(attributed.characters)
        XCTAssertTrue(plain.contains("Bold"))
        XCTAssertTrue(plain.contains("one"))
        let boldRuns = attributed.runs.filter { $0.inlinePresentationIntent?.contains(.stronglyEmphasized) == true }
        XCTAssertFalse(boldRuns.isEmpty, "Expected bold markdown run")
    }

    func testNoteToolExchangeTracksContextUsage() {
        let runtime = ArmyListChatRuntime(workspace: workspace)
        let before = runtime.contextUsage.percentUsed
        let long = String(repeating: "unit line\n", count: 400)
        let capped = runtime.noteToolExchange(name: "searchCatalog", result: long)
        XCTAssertLessThan(capped.count, long.count)
        XCTAssertGreaterThan(runtime.contextUsage.percentUsed, before)
    }

    func testConversationDumpIncludesListAndToolLog() throws {
        let runtime = ArmyListChatRuntime(workspace: workspace)
        _ = ArmyListChatToolExecutor.seedLegalList(
            workspace: workspace,
            battleSizeID: "incursion",
            name: "Dump test"
        )
        runtime.workspace.list = workspace.list
        _ = runtime.noteToolExchange(name: "seedLegalList", result: "Status: LEGAL")
        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.mode, "army-list-chat")
        XCTAssertEqual(dump.list.name, "Dump test")
        XCTAssertEqual(dump.toolLog.count, 1)
        XCTAssertEqual(dump.toolLog[0].name, "seedLegalList")
        XCTAssertFalse(dump.entries.isEmpty)

        let data = try ArmyListChatDumpExporter.jsonData(for: dump)
        let json = try XCTUnwrap(String(data: data, encoding: .utf8))
        XCTAssertTrue(json.contains("\"mode\" : \"army-list-chat\""))
        XCTAssertTrue(json.contains("Dump test"))

        let url = try runtime.writeConversationDumpFile()
        XCTAssertTrue(FileManager.default.fileExists(atPath: url.path))
        XCTAssertTrue(url.lastPathComponent.hasPrefix("army-list-chat-"))
        XCTAssertTrue(url.pathExtension == "json")
    }

    func testAttachAndEnhancementTools() {
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "leagues-of-votann--brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--hearthkyn-warriors",
            models: 10
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--kahl",
            models: 1
        )
        let warriors = try! XCTUnwrap(workspace.list.units.first { $0.datasheetID == "leagues-of-votann--hearthkyn-warriors" })
        let kahl = try! XCTUnwrap(workspace.list.units.first { $0.datasheetID == "leagues-of-votann--kahl" })

        let attach = ArmyListChatToolExecutor.attachCharacter(
            workspace: workspace,
            characterUnitID: kahl.id.uuidString,
            bodyUnitID: warriors.id.uuidString
        )
        XCTAssertTrue(attach.contains("Attached") || attach.contains("LEGAL") || attach.contains("ILLEGAL"))

        let enhancement = ArmyListChatToolExecutor.setEnhancement(
            workspace: workspace,
            unitID: kahl.id.uuidString,
            enhancementID: "leagues-of-votann--brandfast-oathband--precursive-judgement"
        )
        XCTAssertTrue(enhancement.contains("precursive-judgement") || enhancement.contains("Set enhancement"))
        XCTAssertEqual(workspace.list.units.first { $0.id == kahl.id }?.enhancementIDs.first, "leagues-of-votann--brandfast-oathband--precursive-judgement")
    }

    func testRuntimeGateDoesNotCrash() {
        let runtime = ArmyListChatRuntime(workspace: workspace)
        runtime.refreshModelStatus()
        XCTAssertFalse(runtime.modelGate.title.isEmpty)
        XCTAssertFalse(runtime.armyListGateDetail.isEmpty)
    }
}
