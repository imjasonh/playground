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
        _ = ArmyListChatToolExecutor.setBattleSize(workspace: workspace, battleSizeID: "incursion")
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
            prompt: "Fix validation ERRORs only. Never call setBattleSize.",
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

    func testMarkdownInsertsSoftBreaksBeforeLabels() {
        let mashed = "concentrated fire.Countermeasure: Use your speed.Tyranids:Weakness: Swarm."
        let fixed = ArmyListChatMarkdown.insertSoftBreaks(mashed)
        XCTAssertTrue(fixed.contains("fire.\n\nCountermeasure:"), fixed)
        XCTAssertTrue(fixed.contains("Tyranids:\nWeakness:"), fixed)

        let plain = String(ArmyListChatMarkdown.attributed(mashed).characters)
        XCTAssertTrue(plain.contains("Countermeasure:"))
        XCTAssertTrue(
            plain.contains("\n"),
            "Soft breaks should survive into the attributed string: \(plain.debugDescription)"
        )
    }

    func testMarkdownKeepsParagraphSpacing() {
        let attributed = ArmyListChatMarkdown.attributed("First paragraph.\n\nSecond paragraph.")
        let plain = String(attributed.characters)
        XCTAssertTrue(
            plain.contains("First paragraph.\n\nSecond paragraph."),
            "Expected a blank line between paragraphs, got: \(plain.debugDescription)"
        )
    }

    func testMarkdownKeepsSingleLineBreaks() {
        // Default AttributedString markdown collapses single newlines into spaces;
        // the block renderer must keep them so labeled lines stay separate.
        let attributed = ArmyListChatMarkdown.attributed("Line one\nLine two")
        let plain = String(attributed.characters)
        XCTAssertTrue(
            plain.contains("Line one\nLine two"),
            "Expected a line break between lines, got: \(plain.debugDescription)"
        )
    }

    func testMarkdownRendersBulletMarkers() {
        let attributed = ArmyListChatMarkdown.attributed("- one\n- two")
        let plain = String(attributed.characters)
        XCTAssertTrue(plain.contains("•"), "Expected a bullet marker, got: \(plain.debugDescription)")
        XCTAssertFalse(plain.contains("- one"), "Raw bullet syntax should be replaced")
    }

    /// Table of input Markdown to the exact rendered text (bullet markers use a
    /// non-breaking space). This is the primary guard on the chat markdown fix:
    /// spacing, line breaks, bullets, ordered items, headings, inline styles,
    /// and the soft breaks that split run-on model replies.
    func testMarkdownRenderingCases() {
        let bullet = "\u{00A0}"  // trailing non-breaking space after "•"/"1."
        let cases: [(name: String, input: String, expected: String)] = [
            ("paragraph spacing",
             "First paragraph.\n\nSecond paragraph.",
             "First paragraph.\n\nSecond paragraph."),
            ("single line breaks kept",
             "Line one\nLine two",
             "Line one\nLine two"),
            ("dash bullets",
             "- one\n- two",
             "•\(bullet)one\n•\(bullet)two"),
            ("star and plus bullets",
             "* a\n+ b",
             "•\(bullet)a\n•\(bullet)b"),
            ("ordered list",
             "1. first\n2. second",
             "1.\(bullet)first\n2.\(bullet)second"),
            ("bullet keeps inline bold text",
             "- **Kahl** leads",
             "•\(bullet)Kahl leads"),
            ("heading then body",
             "# Heading\nBody text",
             "Heading\nBody text"),
            ("second-level heading",
             "## Sub heading",
             "Sub heading"),
            ("inline bold stripped to text",
             "This is **strong** text",
             "This is strong text"),
            ("inline italic stripped to text",
             "This is *em* text",
             "This is em text"),
            ("sentence then bold heading soft break",
             "Done.**Next:** go",
             "Done.\n\nNext: go"),
            ("label soft break after sentence",
             "fire.Countermeasure: run.",
             "fire.\n\nCountermeasure: run."),
            ("faction then Weakness soft break",
             "Tyranids:Weakness: swarm.",
             "Tyranids:\nWeakness: swarm."),
            ("carriage returns normalized",
             "A\r\nB",
             "A\nB"),
            ("collapses extra blank lines",
             "a\n\n\n\nb",
             "a\n\nb"),
            ("real run-on reply is split",
             "concentrated fire.Countermeasure: Use your speed.Tyranids:Weakness: Swarm.",
             "concentrated fire.\n\nCountermeasure: Use your speed.\n\nTyranids:\nWeakness: Swarm."),
        ]

        for testCase in cases {
            let rendered = String(ArmyListChatMarkdown.attributed(testCase.input).characters)
            XCTAssertEqual(
                rendered,
                testCase.expected,
                "\(testCase.name): \(testCase.input.debugDescription) -> \(rendered.debugDescription)"
            )
        }
    }

    func testBuildPromptFoldsInTheme() {
        let prompt = ArmyListChatPromptComposer.buildPrompt(theme: "night raiders")
        XCTAssertTrue(prompt.contains("applyRosterPlan"))
        XCTAssertTrue(prompt.contains("Theme to honor: night raiders"))
    }

    func testFillPointsPromptFoldsInTheme() {
        let prompt = ArmyListChatPromptComposer.fillPointsPrompt(theme: "veteran survivors")
        XCTAssertTrue(prompt.contains("Fill remaining points"))
        XCTAssertTrue(prompt.contains("Theme to honor: veteran survivors"))
    }

    func testPromptsOmitThemeClauseWhenBlank() {
        XCTAssertFalse(ArmyListChatPromptComposer.buildPrompt(theme: "   ").contains("Theme to honor"))
        XCTAssertFalse(ArmyListChatPromptComposer.fillPointsPrompt(theme: "").contains("Theme to honor"))
    }

    func testStarterPromptListsFactsDetachmentsAndUnits() {
        let prompt = ArmyListStarterPrompt.prompt(
            catalog: catalog,
            factionID: "astra-militarum",
            battleSizeID: "incursion",
            theme: "Armored Company Only Leman russes"
        )
        XCTAssertTrue(prompt.contains("Astra Militarum"), prompt)
        XCTAssertTrue(prompt.contains("1000 pts"), prompt)
        XCTAssertTrue(prompt.contains("applyRosterPlan"), prompt)
        XCTAssertTrue(prompt.contains("Theme: Armored Company Only Leman russes"), prompt)
        // A real detachment id and a theme-matched unit id must appear so the
        // model never has to invent one.
        XCTAssertTrue(prompt.contains("astra-militarum--combined-arms"), prompt)
        XCTAssertTrue(prompt.contains("astra-militarum--leman-russ-battle-tank"), prompt)
    }

    func testStarterPromptFloatsThemeMatchesToTop() {
        let prompt = ArmyListStarterPrompt.prompt(
            catalog: catalog,
            factionID: "astra-militarum",
            battleSizeID: "incursion",
            theme: "leman russ"
        )
        let unitLines = prompt
            .components(separatedBy: "\n")
            .drop { !$0.hasPrefix("Units (") }
            .dropFirst()
            .prefix { $0.contains("pts@") }
        let first = try? XCTUnwrap(unitLines.first)
        XCTAssertTrue((first ?? "").contains("leman-russ"), "Expected a theme match first, got: \(first ?? "none")")
    }

    func testStarterPromptCapsCandidatesAndKeepsACharacter() {
        let prompt = ArmyListStarterPrompt.prompt(
            catalog: catalog,
            factionID: "astra-militarum",
            battleSizeID: "incursion",
            theme: "tanks",
            maxUnits: 12
        )
        let unitLines = prompt
            .components(separatedBy: "\n")
            .filter { $0.contains("pts@") }
        XCTAssertLessThanOrEqual(unitLines.count, 12, "Candidate list must respect maxUnits")
        XCTAssertTrue(unitLines.contains { $0.contains("Character") }, "Palette must include a Character for the Warlord")
    }

    func testStarterPromptOmitsThemeLineWhenBlank() {
        let prompt = ArmyListStarterPrompt.prompt(
            catalog: catalog,
            factionID: "astra-militarum",
            battleSizeID: "incursion",
            theme: "   "
        )
        XCTAssertFalse(prompt.contains("Theme:"), prompt)
        XCTAssertTrue(prompt.contains("applyRosterPlan"), prompt)
        XCTAssertTrue(prompt.contains("pts@"), prompt)
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
        // Simulator CI has no Apple Intelligence welcome line; seed a transcript
        // entry so the dump is never empty when the model gate is unavailable.
        runtime.transcript.append(
            ArmyListChatEntry(kind: .user, text: "Dump fixture prompt")
        )
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

    func testCompactionCarryOverArchivesOlderTurns() {
        var entries: [ArmyListChatEntry] = []
        for i in 1...6 {
            entries.append(ArmyListChatEntry(kind: .user, text: "Ask \(i) about ancient lore"))
            entries.append(ArmyListChatEntry(kind: .assistant, text: "Reply \(i) with unit names"))
        }
        let notes = ArmyListChatRuntime.compactionCarryOver(
            listSnapshot: "Status: LEGAL · 2000 pts",
            transcript: entries
        )
        XCTAssertTrue(notes.contains("Background archive"))
        XCTAssertTrue(notes.contains("Ask 1"))
        XCTAssertTrue(notes.contains("Ask 6"))
        XCTAssertTrue(notes.contains("Recent chat"))
        XCTAssertLessThanOrEqual(notes.count, OnDeviceContextManager.carryOverMaxChars)
    }

    func testRollingSummaryKeepsRecentAndCapsLength() {
        let turns = (1...10).flatMap { i -> [OnDeviceContextManager.Turn] in
            [
                .init(role: .user, content: "User turn \(i) " + String(repeating: "x", count: 80)),
                .init(role: .assistant, content: "Assistant turn \(i) " + String(repeating: "y", count: 80)),
            ]
        }
        let summary = OnDeviceContextManager.rollingSummary(turns: turns, recentCount: 4, maxChars: 900)
        XCTAssertTrue(summary.contains("Background archive"))
        XCTAssertTrue(summary.contains("Recent chat"))
        XCTAssertTrue(summary.contains("User turn 10"))
        XCTAssertLessThanOrEqual(summary.count, 900)
    }

    func testPromptWithCarryOverPrefixesContext() {
        let combined = OnDeviceContextManager.promptWithCarryOver(
            prompt: "Fix errors",
            carryOver: "List snapshot: LEGAL"
        )
        XCTAssertTrue(combined.contains("List snapshot: LEGAL"))
        XCTAssertTrue(combined.contains("Fix errors"))
        XCTAssertEqual(
            OnDeviceContextManager.promptWithCarryOver(prompt: "Hi", carryOver: "  "),
            "Hi"
        )
    }

    func testExceededContextWindowDetection() {
        let ns = NSError(
            domain: "FoundationModels.GenerationError",
            code: -1,
            userInfo: [NSLocalizedDescriptionKey: "failed"]
        )
        XCTAssertTrue(OnDeviceContextManager.isExceededContextWindow(ns))
        let other = NSError(domain: "NSURLErrorDomain", code: -1009, userInfo: nil)
        XCTAssertFalse(OnDeviceContextManager.isExceededContextWindow(other))
        let labeled = NSError(
            domain: "Something",
            code: 1,
            userInfo: [NSLocalizedDescriptionKey: "exceeded context window size"]
        )
        XCTAssertTrue(OnDeviceContextManager.isExceededContextWindow(labeled))
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
