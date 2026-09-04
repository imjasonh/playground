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

    func testAddUnitRejectsOverDuplicateLimit() {
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.clearUnits(workspace: workspace)
        // Non-battleline Incursion cap is 2.
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--cthonian-beserks",
            models: 5
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--cthonian-beserks",
            models: 5
        )
        let rejected = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--cthonian-beserks",
            models: 5
        )
        XCTAssertTrue(rejected.hasPrefix("Rejected:"), rejected)
        XCTAssertEqual(
            workspace.list.units.filter { $0.datasheetID == "leagues-of-votann--cthonian-beserks" }.count,
            2
        )
    }

    func testChipSendShowsTitleNotFullPrompt() async {
        let runtime = ArmyListChatRuntime(workspace: workspace)
        await runtime.send(
            prompt: "Fix validation ERRORs only. Prefer removeUnit.",
            displayText: "Fix errors"
        )
        XCTAssertEqual(runtime.transcript.last { $0.kind == .user }?.text, "Fix errors")
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

    func testLegalSeederBuildsIncursion() throws {
        let seeded = ArmyListLegalSeeder.seed(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            name: "Seeded Votann"
        )
        let result = try XCTUnwrap(seeded)
        XCTAssertEqual(result.list.name, "Seeded Votann")
        XCTAssertEqual(result.list.battleSizeID, "incursion")
        XCTAssertFalse(result.list.units.isEmpty)
        XCTAssertFalse(result.list.detachmentIDs.isEmpty)
        XCTAssertTrue(
            result.validation.isLegal,
            result.validation.errors.map(\.message).joined(separator: "; ")
        )
        XCTAssertLessThanOrEqual(result.validation.totalPoints, 1000)
    }

    func testApplyRosterPlanBuildsCustomCustodesList() throws {
        let list = ArmyListDocument(
            name: "Custodes chat",
            catalogVersion: catalog.version,
            factionID: "adeptus-custodes",
            battleSizeID: "incursion"
        )
        let custodesWorkspace = ArmyListChatWorkspace(list: list, catalog: catalog)
        let output = ArmyListChatToolExecutor.applyRosterPlan(
            workspace: custodesWorkspace,
            battleSizeID: "incursion",
            detachmentIDsCSV: "shield-host",
            unitsCSV: "blade-champion:1,custodian-guard:5,custodian-wardens:5,allarus-custodians:3",
            listName: "Golden Spears"
        )
        XCTAssertTrue(output.contains("Applied roster"), output)
        XCTAssertEqual(custodesWorkspace.list.name, "Golden Spears")
        XCTAssertEqual(custodesWorkspace.list.units.count, 4)
        XCTAssertFalse(custodesWorkspace.list.detachmentIDs.isEmpty)
        XCTAssertLessThanOrEqual(custodesWorkspace.validation.totalPoints, 1000)
    }

    func testLegalSeederBuildsCustodesIncursion() throws {
        let seeded = ArmyListLegalSeeder.seed(
            catalog: catalog,
            factionID: "adeptus-custodes",
            battleSizeID: "incursion",
            name: "Custodes 1k"
        )
        let result = try XCTUnwrap(seeded)
        XCTAssertTrue(
            result.validation.isLegal,
            result.validation.errors.map(\.message).joined(separator: "; ")
        )
        XCTAssertLessThanOrEqual(result.validation.totalPoints, 1000)
        XCTAssertFalse(result.list.units.isEmpty)
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
        _ = ArmyListChatToolExecutor.applyRosterPlan(
            workspace: workspace,
            battleSizeID: "incursion",
            detachmentIDsCSV: "hearthband",
            unitsCSV: "kahl:1,hearthkyn-warriors:10",
            listName: "Dump test"
        )
        runtime.workspace.list = workspace.list
        _ = runtime.noteToolExchange(name: "applyRosterPlan", result: "Status: LEGAL")
        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.mode, "army-list-chat")
        XCTAssertEqual(dump.list.name, "Dump test")
        XCTAssertEqual(dump.toolLog.count, 1)
        XCTAssertEqual(dump.toolLog[0].name, "applyRosterPlan")
        XCTAssertFalse(dump.entries.isEmpty)

        let data = try ArmyListChatDumpExporter.jsonData(for: dump)
        let json = try XCTUnwrap(String(data: data, encoding: .utf8))
        XCTAssertTrue(json.contains("army-list-chat"))
        XCTAssertTrue(json.contains("Dump test"))
        XCTAssertTrue(json.contains("applyRosterPlan"))

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
