import XCTest
@testable import Playground

final class ThermalTests: XCTestCase {
    func testMapsProcessInfoStates() {
        XCTAssertEqual(ThermalLevel(.nominal), .nominal)
        XCTAssertEqual(ThermalLevel(.fair), .fair)
        XCTAssertEqual(ThermalLevel(.serious), .serious)
        XCTAssertEqual(ThermalLevel(.critical), .critical)
    }

    func testShowsLiveActivityOnlyWhenNotNominal() {
        XCTAssertFalse(ThermalLevel.nominal.showsLiveActivity)
        XCTAssertTrue(ThermalLevel.fair.showsLiveActivity)
        XCTAssertTrue(ThermalLevel.serious.showsLiveActivity)
        XCTAssertTrue(ThermalLevel.critical.showsLiveActivity)
    }

    func testSymbolChangesWithLevel() {
        let symbols = Set(ThermalLevel.allCases.map(\.symbolName))
        XCTAssertEqual(symbols.count, ThermalLevel.allCases.count)
    }

    func testTitlesAndAccessibilityNameTheState() {
        for level in ThermalLevel.allCases {
            XCTAssertFalse(level.title.isEmpty, "\(level) needs a title")
            XCTAssertTrue(
                level.accessibilityLabel.contains(level.title),
                "\(level) accessibility label must include the title"
            )
            XCTAssertFalse(level.detail.isEmpty, "\(level) needs detail copy")
        }
    }

    func testPolicyStaysIdleWhenNominalAndNothingPresented() {
        XCTAssertEqual(
            ThermalLiveActivityPolicy.action(presented: nil, incoming: .nominal),
            .none
        )
    }

    func testPolicyStartsWhenHeatBegins() {
        XCTAssertEqual(
            ThermalLiveActivityPolicy.action(presented: nil, incoming: .fair),
            .start(.fair)
        )
        XCTAssertEqual(
            ThermalLiveActivityPolicy.action(presented: nil, incoming: .critical),
            .start(.critical)
        )
    }

    func testPolicyEndsWhenHeatReturnsToNominal() {
        XCTAssertEqual(
            ThermalLiveActivityPolicy.action(presented: .serious, incoming: .nominal),
            .end
        )
    }

    func testPolicyUpdatesWhenNonNominalLevelChanges() {
        XCTAssertEqual(
            ThermalLiveActivityPolicy.action(presented: .fair, incoming: .serious),
            .update(.serious)
        )
    }

    func testPolicyIgnoresUnchangedNonNominalLevel() {
        XCTAssertEqual(
            ThermalLiveActivityPolicy.action(presented: .fair, incoming: .fair),
            .none
        )
    }

    func testStaleDateAddsTenMinutes() {
        let now = Date(timeIntervalSince1970: 1_700_000_000)
        let stale = ThermalLiveActivityPolicy.staleDate(from: now)
        XCTAssertEqual(
            stale.timeIntervalSince(now),
            ThermalLiveActivityPolicy.staleAfter,
            accuracy: 0.001
        )
        XCTAssertEqual(ThermalLiveActivityPolicy.staleAfter, 10 * 60)
    }

    func testDeepLinkBuildsAndParsesThermalURL() throws {
        let url = try XCTUnwrap(ExperimentDeepLink.url(forExperimentID: ThermalLink.experimentID))
        XCTAssertEqual(url.scheme, "playground")
        XCTAssertEqual(url.host, "experiment")
        XCTAssertEqual(ExperimentDeepLink.experimentID(from: url), ThermalLink.experimentID)
    }

    func testDeepLinkRejectsEmptyIdAndUnknownScheme() throws {
        XCTAssertNil(ExperimentDeepLink.url(forExperimentID: ""))
        let other = try XCTUnwrap(URL(string: "https://example.com/thermal"))
        XCTAssertNil(ExperimentDeepLink.experimentID(from: other))
    }

    func testDeepLinkRejectsMissingExperimentPath() throws {
        let url = try XCTUnwrap(URL(string: "playground://experiment"))
        XCTAssertNil(ExperimentDeepLink.experimentID(from: url))
    }

    func testExperimentIdMatchesCatalog() {
        XCTAssertEqual(ThermalExperiment.experiment.id, ThermalLink.experimentID)
        XCTAssertEqual(ThermalExperiment.experiment.title, "Thermal")
    }
}
