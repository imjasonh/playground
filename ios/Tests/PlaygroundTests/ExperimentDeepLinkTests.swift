import XCTest
@testable import Playground

final class ExperimentDeepLinkTests: XCTestCase {
    func testDeepLinkBuildsAndParsesExperimentURL() throws {
        let url = try XCTUnwrap(ExperimentDeepLink.url(forExperimentID: "ride-monitor"))
        XCTAssertEqual(url.scheme, "playground")
        XCTAssertEqual(url.host, "experiment")
        XCTAssertEqual(ExperimentDeepLink.experimentID(from: url), "ride-monitor")
    }

    func testDeepLinkRejectsEmptyIdAndUnknownScheme() throws {
        XCTAssertNil(ExperimentDeepLink.url(forExperimentID: ""))
        let other = try XCTUnwrap(URL(string: "https://example.com/ride-monitor"))
        XCTAssertNil(ExperimentDeepLink.experimentID(from: other))
    }

    func testDeepLinkRejectsMissingExperimentPath() throws {
        let url = try XCTUnwrap(URL(string: "playground://experiment"))
        XCTAssertNil(ExperimentDeepLink.experimentID(from: url))
    }
}
