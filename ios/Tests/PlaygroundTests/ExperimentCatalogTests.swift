import XCTest
@testable import Playground

final class ExperimentCatalogTests: XCTestCase {
    func testCatalogIsNotEmpty() {
        XCTAssertFalse(ExperimentCatalog.all.isEmpty)
    }

    func testExperimentIDsAreUniqueAndNonEmpty() {
        let ids = ExperimentCatalog.all.map(\.id)
        XCTAssertEqual(Set(ids).count, ids.count, "Experiment ids must be unique")
        XCTAssertFalse(ids.contains(where: \.isEmpty), "Experiment ids must be non-empty")
    }

    func testEveryExperimentHasTitleAndSummary() {
        for experiment in ExperimentCatalog.all {
            XCTAssertFalse(experiment.title.isEmpty, "\(experiment.id) needs a title")
            XCTAssertFalse(experiment.summary.isEmpty, "\(experiment.id) needs a summary")
            XCTAssertFalse(experiment.icon.isEmpty, "\(experiment.id) needs an icon")
        }
    }

    func testIncludesTheTemperatureConverter() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "temperature-converter" })
    }
}
