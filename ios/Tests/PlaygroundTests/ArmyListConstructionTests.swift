import XCTest
@testable import Playground

@MainActor
final class ArmyListConstructionTests: XCTestCase {
    private var catalog: ArmyCatalog!

    override func setUpWithError() throws {
        catalog = try ArmyListCatalogTests.loadCatalogFromRepo()
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
