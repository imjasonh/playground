import XCTest
@testable import Playground

@MainActor
final class ArmyListConstructionTests: XCTestCase {
    private var catalog: ArmyCatalog!

    override func setUpWithError() throws {
        catalog = try ArmyListCatalogTests.loadCatalogFromRepo()
        ArmyListThemeBriefBuilder.foundationModelsEnabled = false
        ArmyListThemeBriefBuilder.testOverride = nil
    }

    override func tearDown() {
        ArmyListThemeBriefBuilder.testOverride = nil
        ArmyListThemeBriefBuilder.foundationModelsEnabled = true
        super.tearDown()
    }

    func testGreedyBuildsLegalVotannIncursion() async {
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            theme: "hearthkyn",
            userName: "Test list",
            decider: LayaGreedyDecider()
        )
        let built = try! XCTUnwrap(result)
        let validation = ArmyListValidator.validate(list: built.list, catalog: catalog)
        XCTAssertTrue(validation.isLegal, "\(validation.errors.map(\.message))")
        XCTAssertFalse(built.list.units.isEmpty)
        XCTAssertNotNil(built.list.warlordUnitID)
        XCTAssertLessThanOrEqual(validation.totalPoints, 1000)
        XCTAssertGreaterThan(validation.totalPoints, 200)
        XCTAssertEqual(built.list.name, "Test list")
        XCTAssertFalse(built.usedLaya)
        XCTAssertFalse(built.steps.isEmpty)
        XCTAssertFalse(built.steps.contains { $0.worker == .laya })
    }

    func testGreedyBuildsLegalCustodesIncursion() async {
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "adeptus-custodes",
            battleSizeID: "incursion",
            theme: "",
            userName: nil,
            decider: LayaGreedyDecider()
        )
        let built = try! XCTUnwrap(result)
        let validation = ArmyListValidator.validate(list: built.list, catalog: catalog)
        XCTAssertTrue(validation.isLegal, "\(validation.errors.map(\.message))")
        XCTAssertLessThanOrEqual(validation.totalPoints, 1000)
        XCTAssertTrue(ArmyListPalette.hasCharacter(list: built.list, catalog: catalog))
    }

    func testStarterBuilderUsesInjectedDecider() async {
        let list = await ArmyListStarterBuilder.build(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            theme: "",
            userName: "Injected",
            decider: LayaGreedyDecider()
        )
        let built = try! XCTUnwrap(list)
        XCTAssertTrue(ArmyListValidator.validate(list: built, catalog: catalog).isLegal)
        XCTAssertEqual(built.name, "Injected")
    }

    func testFillAddsUnitsWithoutExceedingLimit() async {
        let workspace = ArmyListChatWorkspace(
            list: ArmyListDocument(
                name: "Fill",
                catalogVersion: catalog.version,
                factionID: "leagues-of-votann",
                battleSizeID: "incursion"
            ),
            catalog: catalog
        )
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "leagues-of-votann--brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--kahl",
            models: 1
        )
        let before = workspace.validation.totalPoints
        let result = await ArmyListDecisionController.fill(
            workspace: workspace,
            theme: "hearthkyn",
            decider: LayaGreedyDecider()
        )
        let filled = try! XCTUnwrap(result)
        XCTAssertTrue(workspace.validation.isLegal, "\(workspace.validation.errors.map(\.message))")
        XCTAssertGreaterThan(workspace.validation.totalPoints, before)
        XCTAssertLessThanOrEqual(workspace.validation.totalPoints, 1000)
        XCTAssertEqual(filled.list.units.count, workspace.list.units.count)
    }

    func testFixSetsMissingWarlord() async {
        let workspace = ArmyListChatWorkspace(
            list: ArmyListDocument(
                name: "Fix",
                catalogVersion: catalog.version,
                factionID: "leagues-of-votann",
                battleSizeID: "incursion"
            ),
            catalog: catalog
        )
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "leagues-of-votann--brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--kahl",
            models: 1
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--hearthkyn-warriors",
            models: 10
        )
        var list = workspace.list
        list.warlordUnitID = nil
        workspace.replaceList(list)
        XCTAssertTrue(workspace.validation.errors.contains { $0.code == "warlord.missing" })

        let result = await ArmyListDecisionController.fix(
            workspace: workspace,
            theme: "",
            decider: LayaGreedyDecider()
        )
        XCTAssertNotNil(result)
        XCTAssertNotNil(workspace.list.warlordUnitID)
        XCTAssertFalse(workspace.validation.errors.contains { $0.code == "warlord.missing" })
    }

    func testSnapshotStaysShort() {
        let list = ArmyListDocument(
            name: "Snap",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion"
        )
        let text = ArmyListLayaSnapshot.text(list: list, catalog: catalog, theme: "hearthkyn bikes")
        XCTAssertLessThanOrEqual(text.count, ArmyListLayaSnapshot.maxCharacters)
        XCTAssertTrue(text.contains("Votann") || text.contains("Incursion"), text)
        XCTAssertTrue(text.contains("Theme"), text)
    }

    func testLegalAddsHaveUniqueLabelsAndCap() {
        let list = ArmyListDocument(
            name: "Moves",
            catalogVersion: catalog.version,
            factionID: "astra-militarum",
            battleSizeID: "incursion"
        )
        let moves = ArmyListPalette.legalAdds(
            catalog: catalog,
            list: list,
            theme: "leman russ",
            remainingPoints: 1000,
            hasCharacter: false,
            charactersOnly: true
        )
        XCTAssertLessThanOrEqual(moves.count, ArmyListPalette.maxLayaOptions)
        XCTAssertEqual(Set(moves.map(\.label)).count, moves.count)
        XCTAssertTrue(moves.allSatisfy { $0.sheet.characterRole != nil })
    }

    func testThemeRankFloatsLemanRuss() {
        let ranked = ArmyListPalette.rankedSheets(
            catalog: catalog,
            factionID: "astra-militarum",
            theme: "leman russ"
        )
        let first = try! XCTUnwrap(ranked.first)
        XCTAssertTrue(first.sheet.id.contains("leman-russ"), first.sheet.id)
    }

    func testTitanLegionsStillInfeasibleAtIncursion() {
        XCTAssertNotNil(
            ArmyListStarterPrompt.buildFeasibilityIssue(
                catalog: catalog,
                factionID: "titan-legions",
                battleSizeID: "incursion"
            )
        )
    }

    func testStarterBuildReturnsNilWhenCancelledBeforeWork() async {
        let catalog = self.catalog!
        let task = Task { @MainActor () -> ArmyListDocument? in
            await ArmyListStarterBuilder.build(
                catalog: catalog,
                factionID: "leagues-of-votann",
                battleSizeID: "incursion",
                theme: "",
                userName: nil,
                decider: LayaGreedyDecider()
            )
        }
        task.cancel()
        let built = await task.value
        XCTAssertNil(built)
    }

    func testLegalEnhancementsForVotannKahl() {
        let workspace = ArmyListChatWorkspace(
            list: ArmyListDocument(
                name: "Enh",
                catalogVersion: catalog.version,
                factionID: "leagues-of-votann",
                battleSizeID: "incursion"
            ),
            catalog: catalog
        )
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "leagues-of-votann--brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--kahl",
            models: 1
        )
        let kahl = try! XCTUnwrap(workspace.list.units.first)
        var list = workspace.list
        list.warlordUnitID = kahl.id
        workspace.replaceList(list)

        let moves = ArmyListPalette.legalEnhancements(
            catalog: catalog,
            list: workspace.list,
            theme: "",
            remainingPoints: 800,
            remainingPicks: 2
        )
        XCTAssertFalse(moves.isEmpty)
        XCTAssertTrue(moves.contains { $0.enhancement.id.contains("signature-restoration") })
        XCTAssertEqual(Set(moves.map(\.label)).count, moves.count)
        XCTAssertTrue(moves.allSatisfy { !$0.enhancement.isUpgrade })
    }

    func testGreedyBuildAssignsEnhancementWhenPointsRemain() async {
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            theme: "",
            userName: nil,
            decider: LayaGreedyDecider()
        )
        let built = try! XCTUnwrap(result)
        let picks = ArmyListPalette.enhancementPickSlots(list: built.list, catalog: catalog)
        let leftover = ArmyListPalette.legalEnhancements(
            catalog: catalog,
            list: built.list,
            theme: "",
            remainingPoints: max(0, 1000 - ArmyListValidator.validate(list: built.list, catalog: catalog).totalPoints),
            remainingPicks: 2 - picks
        )
        XCTAssertTrue(
            picks > 0 || leftover.isEmpty,
            "Expected a pick or no remaining legal enhancement: picks=\(picks) leftover=\(leftover.map(\.label))"
        )
        XCTAssertTrue(built.steps.contains { $0.title == "Enhancement" } || leftover.isEmpty)
    }

    func testFixClearsIllegalEnhancement() async {
        let workspace = ArmyListChatWorkspace(
            list: ArmyListDocument(
                name: "Fix enh",
                catalogVersion: catalog.version,
                factionID: "leagues-of-votann",
                battleSizeID: "incursion"
            ),
            catalog: catalog
        )
        _ = ArmyListChatToolExecutor.setDetachments(
            workspace: workspace,
            detachmentIDsCSV: "leagues-of-votann--brandfast-oathband"
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--kahl",
            models: 1
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "leagues-of-votann--hearthkyn-warriors",
            models: 10
        )
        let kahl = try! XCTUnwrap(
            workspace.list.units.first { $0.datasheetID == "leagues-of-votann--kahl" }
        )
        _ = ArmyListChatToolExecutor.setWarlord(
            workspace: workspace,
            unitID: kahl.id.uuidString
        )
        let warriors = try! XCTUnwrap(
            workspace.list.units.first { $0.datasheetID == "leagues-of-votann--hearthkyn-warriors" }
        )
        _ = ArmyListChatToolExecutor.setEnhancement(
            workspace: workspace,
            unitID: warriors.id.uuidString,
            enhancementID: "leagues-of-votann--brandfast-oathband--signature-restoration"
        )
        XCTAssertTrue(workspace.validation.errors.contains { $0.code == "enhancement.requiresCharacter" })

        let result = await ArmyListDecisionController.fix(
            workspace: workspace,
            theme: "",
            decider: LayaGreedyDecider()
        )
        XCTAssertNotNil(result)
        XCTAssertFalse(workspace.validation.errors.contains { $0.code == "enhancement.requiresCharacter" })
        XCTAssertTrue(workspace.list.units[0].enhancementIDs.isEmpty)
    }

    func testBattlelineBoostsWhenRosterHasNone() {
        let list = ArmyListDocument(
            name: "BL",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion"
        )
        XCTAssertFalse(ArmyListPalette.hasBattleline(list: list, catalog: catalog))
        let moves = ArmyListPalette.legalAdds(
            catalog: catalog,
            list: list,
            theme: "",
            remainingPoints: 1000,
            hasCharacter: true,
            charactersOnly: false
        )
        XCTAssertTrue(
            moves.contains { $0.sheet.battleline },
            "Empty-roster shortlist should include Battleline: \(moves.map(\.label))"
        )
    }

    func testScriptedDeciderPicksNamedDetachment() async {
        let decider = LayaScriptedDecider(preferredLabels: ["Farseekers"])
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            theme: "",
            userName: nil,
            decider: decider
        )
        let built = try! XCTUnwrap(result)
        XCTAssertTrue(
            built.list.detachmentIDs.contains { $0.contains("farseekers") },
            "\(built.list.detachmentIDs)"
        )
    }

    func testHeuristicPromptTokensKeepMonsterSwarm() {
        let brief = ArmyListThemeBriefBuilder.heuristic(
            catalog: catalog,
            prompt: "tyranid monster swarm",
            list: ArmyListDocument(
                name: "T",
                catalogVersion: catalog.version,
                factionID: "tyranids",
                battleSizeID: "incursion"
            )
        )
        XCTAssertEqual(brief.source, .prompt)
        XCTAssertTrue(brief.tokens.contains("monster"), "\(brief.tokens)")
        XCTAssertTrue(brief.tokens.contains("swarm"), "\(brief.tokens)")
        XCTAssertTrue(brief.snapshotTheme.lowercased().contains("monster"))
    }

    func testHeuristicRosterTokensReadOutriders() {
        let workspace = ArmyListChatWorkspace(
            list: ArmyListDocument(
                name: "Bikes",
                catalogVersion: catalog.version,
                factionID: "space-marines",
                battleSizeID: "incursion"
            ),
            catalog: catalog
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "space-marines--outrider-squad",
            models: 3
        )
        let brief = ArmyListThemeBriefBuilder.heuristic(
            catalog: catalog,
            prompt: "",
            list: workspace.list
        )
        XCTAssertEqual(brief.source, .roster)
        XCTAssertTrue(brief.tokens.contains("outrider"), "\(brief.tokens)")
        XCTAssertFalse(brief.tokens.contains("squad"), "\(brief.tokens)")
    }

    func testMakeUsesRosterWhenPromptBlankAndModelOff() async {
        let workspace = ArmyListChatWorkspace(
            list: ArmyListDocument(
                name: "Bikes",
                catalogVersion: catalog.version,
                factionID: "space-marines",
                battleSizeID: "incursion"
            ),
            catalog: catalog
        )
        _ = ArmyListChatToolExecutor.addUnit(
            workspace: workspace,
            datasheetID: "space-marines--outrider-squad",
            models: 3
        )
        let brief = await ArmyListThemeBriefBuilder.make(
            catalog: catalog,
            factionID: "space-marines",
            prompt: "",
            list: workspace.list
        )
        XCTAssertEqual(brief.source, .roster)
        XCTAssertTrue(brief.tokens.contains("outrider"), "\(brief.tokens)")
    }

    func testFoundationThemeBriefExpandsRankingTowardOutriders() async {
        ArmyListThemeBriefBuilder.testOverride = { _ in
            ArmyListThemeBrief(
                prompt: "white scars fast attack",
                tokens: ["bike", "outrider", "jump"],
                summary: "White Scars bikes and jump troops",
                source: .foundationModels
            )
        }
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "space-marines",
            battleSizeID: "incursion",
            theme: "white scars fast attack",
            userName: nil,
            decider: LayaGreedyDecider()
        )
        let built = try! XCTUnwrap(result)
        XCTAssertEqual(built.themeBrief.source, .foundationModels)
        XCTAssertTrue(built.themeBrief.tokens.contains("outrider"))
        XCTAssertTrue(built.summary.contains("White Scars"))
        XCTAssertTrue(built.steps.contains { $0.worker == .foundationModels && $0.title == "Theme" })
        XCTAssertNil(built.themeScoreLabel)
        XCTAssertEqual(built.list.name, "White Scars bikes and jump troops")
        XCTAssertFalse(built.steps.contains { $0.worker == .laya })
        let ranked = ArmyListPalette.rankedSheets(
            catalog: catalog,
            factionID: "space-marines",
            theme: built.themeBrief.rankingText
        )
        XCTAssertTrue(
            ranked.prefix(8).contains { $0.sheet.id.contains("outrider") },
            "\(ranked.prefix(8).map(\.sheet.id))"
        )
    }

    func testGreedySkipsOffThemeNonCharacters() async {
        ArmyListThemeBriefBuilder.testOverride = { _ in
            ArmyListThemeBrief(
                prompt: "hearthkyn",
                tokens: ["hearthkyn"],
                summary: "Hearthkyn infantry",
                source: .prompt
            )
        }
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            theme: "hearthkyn",
            userName: nil,
            decider: LayaGreedyDecider()
        )
        let built = try! XCTUnwrap(result)
        let extras = built.list.units.compactMap { unit -> DatasheetDefinition? in
            guard let sheet = catalog.datasheet(id: unit.datasheetID) else { return nil }
            return sheet.characterRole == nil ? sheet : nil
        }
        XCTAssertFalse(extras.isEmpty)
        XCTAssertTrue(
            extras.allSatisfy { ArmyListPalette.matchesTheme(sheet: $0, tokens: ["hearthkyn"]) },
            "\(extras.map(\.name))"
        )
        XCTAssertTrue(built.steps.contains { $0.title == "Theme" && $0.worker == .mechanical })
        XCTAssertFalse(built.steps.contains { $0.title == "On theme" && $0.worker == .laya })
        XCTAssertTrue(built.steps.contains { $0.title == "Add unit" })
    }

    func testLayaNoulRejectsNamedUnit() async {
        ArmyListThemeBriefBuilder.testOverride = { _ in
            ArmyListThemeBrief(
                prompt: "",
                tokens: ["bike"],
                summary: "Bikes",
                source: .foundationModels
            )
        }
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            theme: "",
            userName: nil,
            decider: LayaNoulRejectDecider(rejectName: "Hearthkyn Warriors"),
            usedLaya: true
        )
        let built = try! XCTUnwrap(result)
        XCTAssertFalse(
            built.list.units.contains { $0.datasheetID.contains("hearthkyn-warriors") },
            "\(built.list.units.map(\.datasheetID))"
        )
        XCTAssertTrue(
            built.steps.contains { $0.title == "On theme" && $0.applied.contains("Off-theme: Hearthkyn Warriors") }
        )
        let validation = ArmyListValidator.validate(list: built.list, catalog: catalog)
        XCTAssertTrue(validation.isLegal, "\(validation.errors.map(\.message))")
    }

    func testSnapshotUsesThemeBriefSummary() {
        let list = ArmyListDocument(
            name: "Snap",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion"
        )
        let text = ArmyListLayaSnapshot.text(
            list: list,
            catalog: catalog,
            theme: "White Scars bikes and jump troops"
        )
        XCTAssertTrue(text.contains("White Scars bikes"), text)
        XCTAssertLessThanOrEqual(text.count, ArmyListLayaSnapshot.maxCharacters)
    }

    func testThemeBriefPromptIsShort() {
        let prompt = ArmyListThemeBriefBuilder.prompt(
            for: ArmyListThemeBriefBuilder.Input(
                factionName: "Space Marines",
                prompt: "white scars fast attack",
                rosterNames: ["Outrider Squad"]
            )
        )
        XCTAssertTrue(prompt.contains("Faction: Space Marines"), prompt)
        XCTAssertTrue(prompt.contains("white scars fast attack"), prompt)
        XCTAssertTrue(prompt.contains("Outrider Squad"), prompt)
        XCTAssertTrue(prompt.contains("list name"), prompt)
        XCTAssertLessThan(prompt.count, 800)
    }

    func testMatchesThemeEmptyTokensAlwaysTrue() {
        let sheet = try! XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--kahl"))
        XCTAssertTrue(ArmyListPalette.matchesTheme(sheet: sheet, tokens: []))
        XCTAssertFalse(ArmyListPalette.matchesTheme(sheet: sheet, tokens: ["hearthkyn"]))
    }

    func testChoiceWorkerIsMechanicalForOneOption() {
        XCTAssertEqual(ArmyListHarness.choiceWorker(optionCount: 1, usedLaya: true), .mechanical)
        XCTAssertEqual(ArmyListHarness.choiceWorker(optionCount: 2, usedLaya: true), .laya)
        XCTAssertEqual(ArmyListHarness.choiceWorker(optionCount: 2, usedLaya: false), .mechanical)
    }

    func testPreferThemedKeepsOnlyHitsWhenAnyExist() {
        let warriors = try! XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--hearthkyn-warriors"))
        let kahl = try! XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--kahl"))
        let kept = ArmyListHarness.preferThemed([kahl, warriors], tokens: ["hearthkyn"]) { sheet in
            ArmyListPalette.matchesTheme(sheet: sheet, tokens: ["hearthkyn"])
        }
        XCTAssertEqual(kept.map(\.id), [warriors.id])
    }

    func testPreferThemedLeavesPoolWhenNothingHits() {
        let kahl = try! XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--kahl"))
        let kept = ArmyListHarness.preferThemed([kahl], tokens: ["bike"]) { sheet in
            ArmyListPalette.matchesTheme(sheet: sheet, tokens: ["bike"])
        }
        XCTAssertEqual(kept.map(\.id), [kahl.id])
    }

    func testThemeRouteFarmsOverlapToCatalog() {
        let kahl = try! XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--kahl"))
        let warriors = try! XCTUnwrap(catalog.datasheet(id: "leagues-of-votann--hearthkyn-warriors"))
        XCTAssertEqual(
            ArmyListHarness.themeRoute(
                sheet: warriors,
                tokens: ["hearthkyn"],
                usedLaya: true,
                requireCharacter: false,
                remainingAlternatives: 1
            ),
            .accept
        )
        XCTAssertEqual(
            ArmyListHarness.themeRoute(
                sheet: kahl,
                tokens: ["hearthkyn"],
                usedLaya: true,
                requireCharacter: false,
                remainingAlternatives: 1
            ),
            .askLaya
        )
        XCTAssertEqual(
            ArmyListHarness.themeRoute(
                sheet: kahl,
                tokens: ["hearthkyn"],
                usedLaya: false,
                requireCharacter: false,
                remainingAlternatives: 1
            ),
            .reject
        )
        XCTAssertEqual(
            ArmyListHarness.themeRoute(
                sheet: kahl,
                tokens: ["hearthkyn"],
                usedLaya: false,
                requireCharacter: true,
                remainingAlternatives: 0
            ),
            .accept
        )
    }

    func testShouldAskToKeepAddingOnlyInLeftoverBand() {
        XCTAssertFalse(
            ArmyListHarness.shouldAskToKeepAdding(
                hasCharacter: true,
                remainingPoints: 20,
                cheapestLegal: 40
            )
        )
        XCTAssertTrue(
            ArmyListHarness.shouldAskToKeepAdding(
                hasCharacter: true,
                remainingPoints: 50,
                cheapestLegal: 40
            )
        )
        XCTAssertFalse(
            ArmyListHarness.shouldAskToKeepAdding(
                hasCharacter: true,
                remainingPoints: 200,
                cheapestLegal: 40
            )
        )
        XCTAssertFalse(
            ArmyListHarness.shouldAskToKeepAdding(
                hasCharacter: false,
                remainingPoints: 50,
                cheapestLegal: 40
            )
        )
    }

    func testCutCandidatesOrdersOffThemeBeforeOnTheme() {
        let warlordID = UUID()
        let fortressID = UUID()
        let warriorsID = UUID()
        var list = ArmyListDocument(
            name: "Cut",
            catalogVersion: catalog.version,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion"
        )
        list.warlordUnitID = warlordID
        list.units = [
            ListUnitInstance(id: warlordID, datasheetID: "leagues-of-votann--kahl", models: 1),
            ListUnitInstance(
                id: fortressID,
                datasheetID: "leagues-of-votann--hekaton-land-fortress",
                models: 1
            ),
            ListUnitInstance(
                id: warriorsID,
                datasheetID: "leagues-of-votann--hearthkyn-warriors",
                models: 10
            ),
        ]
        let cut = ArmyListHarness.cutCandidates(
            list: list,
            catalog: catalog,
            tokens: ["hearthkyn"],
            limit: 8
        )
        XCTAssertEqual(cut.first?.id, fortressID, "\(cut.map(\.datasheetID))")
        XCTAssertFalse(cut.contains { $0.id == warlordID })
    }

    func testUsedLayaRecordsThemeScore() async {
        ArmyListThemeBriefBuilder.testOverride = { _ in
            ArmyListThemeBrief(
                prompt: "hearthkyn",
                tokens: ["hearthkyn"],
                summary: "Hearthkyn infantry",
                source: .prompt
            )
        }
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            theme: "hearthkyn",
            userName: nil,
            decider: LayaScoreStubDecider(),
            usedLaya: true
        )
        let built = try! XCTUnwrap(result)
        XCTAssertEqual(built.themeScoreLabel, "strong")
        XCTAssertTrue(built.summary.contains("Theme score: strong"), built.summary)
        XCTAssertTrue(built.steps.contains { $0.title == "Theme score" && $0.worker == .laya })
    }

    func testLegalModelCountsOffersBothSacresantSizes() {
        let list = ArmyListDocument(
            name: "Sizes",
            catalogVersion: catalog.version,
            factionID: "adepta-sororitas",
            battleSizeID: "incursion"
        )
        let sheet = try! XCTUnwrap(catalog.datasheet(id: "adepta-sororitas--celestian-sacresants"))
        let sizes = ArmyListPalette.legalModelCounts(
            sheet: sheet,
            list: list,
            remainingPoints: 1000
        )
        XCTAssertEqual(sizes.map(\.models), [10, 5])
        XCTAssertTrue(sizes[0].points > sizes[1].points)
    }

    func testListNamePrefersFoundationNameThenSummary() {
        let named = ArmyListThemeBrief(
            prompt: "white scars",
            tokens: ["bike"],
            summary: "White Scars bikes and jump troops",
            source: .foundationModels,
            listName: "White Scars Outriders"
        )
        XCTAssertEqual(
            ArmyListDecisionController.listName(
                catalog: catalog,
                factionID: "space-marines",
                battleSizeID: "incursion",
                theme: "white scars",
                userName: nil,
                brief: named
            ),
            "White Scars Outriders"
        )
        let fromSummary = ArmyListThemeBrief(
            prompt: "white scars",
            tokens: ["bike"],
            summary: "White Scars bikes and jump troops",
            source: .foundationModels
        )
        XCTAssertEqual(
            ArmyListDecisionController.listName(
                catalog: catalog,
                factionID: "space-marines",
                battleSizeID: "incursion",
                theme: "white scars",
                userName: nil,
                brief: fromSummary
            ),
            "White Scars bikes and jump troops"
        )
        XCTAssertEqual(
            ArmyListDecisionController.listName(
                catalog: catalog,
                factionID: "space-marines",
                battleSizeID: "incursion",
                theme: "white scars",
                userName: "My list",
                brief: named
            ),
            "My list"
        )
    }

    func testLayaCanSkipEnhancements() async {
        let result = await ArmyListDecisionController.build(
            catalog: catalog,
            factionID: "leagues-of-votann",
            battleSizeID: "incursion",
            theme: "",
            userName: nil,
            decider: LayaNoulRejectDecider(rejectName: "Assign an enhancement"),
            usedLaya: true
        )
        let built = try! XCTUnwrap(result)
        XCTAssertFalse(
            built.steps.contains { $0.title == "Enhancement" && $0.applied.contains(" on ") }
        )
        let validation = ArmyListValidator.validate(list: built.list, catalog: catalog)
        XCTAssertTrue(validation.isLegal, "\(validation.errors.map(\.message))")
    }
}

@MainActor
final class LayaScriptedDecider: LayaDeciding {
    var preferredLabels: [String]

    init(preferredLabels: [String]) {
        self.preferredLabels = preferredLabels
    }

    func decide(state: String, question: LayaQuestion) async throws -> LayaDecision {
        if case .choice(_, let options) = question,
           let want = preferredLabels.first,
           options.contains(where: { $0.label == want })
        {
            preferredLabels.removeFirst()
            return LayaGreedyDecider.choice(label: want, options: options, act: 1)
        }
        return try await LayaGreedyDecider().decide(state: state, question: question)
    }
}

@MainActor
final class LayaNoulRejectDecider: LayaDeciding {
    let rejectName: String

    init(rejectName: String) {
        self.rejectName = rejectName
    }

    func decide(state: String, question: LayaQuestion) async throws -> LayaDecision {
        if case .noul(let instructions, _, _) = question {
            let p: Double = instructions.localizedCaseInsensitiveContains(rejectName) ? 0.05 : 0.9
            return LayaGreedyDecider.noul(probability: p)
        }
        return try await LayaGreedyDecider().decide(state: state, question: question)
    }
}

@MainActor
final class LayaScoreStubDecider: LayaDeciding {
    func decide(state: String, question: LayaQuestion) async throws -> LayaDecision {
        if case .score = question {
            let levels = ArmyListHarness.themeScoreLevels
            return LayaDecision(
                kind: .score,
                answer: .score(
                    value: 3,
                    probabilities: [0, 0, 0, 1, 0],
                    legend: levels
                ),
                confidence: 1,
                actProbability: 1
            )
        }
        return try await LayaGreedyDecider().decide(state: state, question: question)
    }
}
