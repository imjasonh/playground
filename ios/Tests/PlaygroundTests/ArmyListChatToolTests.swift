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

    func testSeedLegalListBuildsCustodesIncursion() throws {
        let list = ArmyListDocument(
            name: "Custodes chat",
            catalogVersion: catalog.version,
            factionID: "adeptus-custodes",
            battleSizeID: "incursion"
        )
        let custodesWorkspace = ArmyListChatWorkspace(list: list, catalog: catalog)
        let output = ArmyListChatToolExecutor.seedLegalList(
            workspace: custodesWorkspace,
            battleSizeID: "incursion",
            name: "Custodes 1k"
        )
        XCTAssertFalse(output.contains("Could not seed"), output)
        let result = custodesWorkspace.validation
        XCTAssertTrue(
            result.isLegal,
            result.errors.map(\.message).joined(separator: "; ")
        )
        XCTAssertLessThanOrEqual(result.totalPoints, 1000)
        XCTAssertFalse(custodesWorkspace.list.units.isEmpty)
    }

    func testBuildLegalIncursionChipBypassesModel() async {
        let runtime = ArmyListChatRuntime(workspace: workspace)
        await runtime.buildLegalIncursion(name: "Chip 1k")
        XCTAssertEqual(workspace.list.name, "Chip 1k")
        XCTAssertTrue(workspace.validation.isLegal, workspace.validation.errors.map(\.message).joined(separator: "; "))
        XCTAssertTrue(runtime.transcript.contains { $0.kind == .user && $0.text == "Build 1k" })
        XCTAssertTrue(runtime.transcript.contains { $0.kind == .tool && $0.text.contains("seedLegalList") })
        XCTAssertTrue(runtime.transcript.contains { $0.kind == .assistant && $0.text.contains("LEGAL") })
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
        XCTAssertTrue(json.contains("army-list-chat"))
        XCTAssertTrue(json.contains("Dump test"))
        XCTAssertTrue(json.contains("seedLegalList"))

        let url = try runtime.writeConversationDumpFile()
        XCTAssertTrue(FileManager.default.fileExists(atPath: url.path))
        XCTAssertTrue(url.lastPathComponent.hasPrefix("army-list-chat-"))
        XCTAssertTrue(url.pathExtension == "json")
    }

    func testCompactionCarryOverKeepsRecentTurnsAndLatestInstruction() {
        let entries = [
            ArmyListChatEntry(kind: .user, text: "Theme only: suggest a name"),
            ArmyListChatEntry(kind: .assistant, text: "Call it Hearthguard. Paint ochre."),
            ArmyListChatEntry(kind: .user, text: "Weaknesses only: matchups?"),
        ]
        let notes = ArmyListChatRuntime.compactionCarryOver(
            listSnapshot: "Status: LEGAL · 1000 pts",
            transcript: entries
        )
        XCTAssertTrue(notes.contains("Answer ONLY the latest user message"))
        XCTAssertTrue(notes.contains("Status: LEGAL"))
        XCTAssertTrue(notes.contains("Theme only"))
        XCTAssertTrue(notes.contains("Weaknesses only"))
        XCTAssertTrue(notes.contains("Hearthguard"))
    }

    func testToolDisplayLabelsIncludeUnitName() {
        let add = ArmyListChatToolDisplay.label(
            name: "addUnit",
            result: "Added Hearthkyn Warriors ×10 (id ABC).\nStatus: LEGAL · 200 pts"
        )
        XCTAssertEqual(add, "addUnit · Hearthkyn Warriors ×10")

        let search = ArmyListChatToolDisplay.label(
            name: "searchCatalog",
            result: "unit a\nunit b\nunit c"
        )
        XCTAssertEqual(search, "searchCatalog · 3 hits")

        let summary = ArmyListChatToolDisplay.groupSummary(labels: [
            "addUnit · Hearthkyn Warriors ×10",
            "addUnit · Kâhl ×1",
            "setWarlord · set",
        ])
        XCTAssertTrue(summary.contains("3 actions"))
        XCTAssertTrue(summary.contains("Hearthkyn"))
    }

    func testTranscriptBlocksCollapseConsecutiveTools() {
        let u = ArmyListChatEntry(kind: .user, text: "Build")
        let t1 = ArmyListChatEntry(kind: .tool, text: "addUnit · Warriors ×10")
        let t2 = ArmyListChatEntry(kind: .tool, text: "setWarlord · set")
        let a = ArmyListChatEntry(kind: .assistant, text: "Done")
        let blocks = ArmyListChatTranscriptBlock.build(from: [u, t1, t2, a])
        XCTAssertEqual(blocks.count, 3)
        guard case .message(let user) = blocks[0] else {
            return XCTFail("expected user message")
        }
        XCTAssertEqual(user.kind, .user)
        guard case .tools(_, let tools) = blocks[1] else {
            return XCTFail("expected tools group")
        }
        XCTAssertEqual(tools.count, 2)
        guard case .message(let assistant) = blocks[2] else {
            return XCTFail("expected assistant message")
        }
        XCTAssertEqual(assistant.kind, .assistant)
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
