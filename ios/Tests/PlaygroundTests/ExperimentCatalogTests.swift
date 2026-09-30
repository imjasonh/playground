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

    func testIncludesRideMonitor() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "ride-monitor" })
    }

    func testIncludesT9Keyboard() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "t9-keyboard" })
    }

    func testIncludesFollowTheHum() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "follow-the-hum" })
    }

    func testIncludesVoxelWorld() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "voxel-world" })
    }

    func testIncludesWigglecam() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "wigglecam" })
    }

    func testIncludesLocalLens() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "local-lens" })
    }

    func testIncludesLiveTranslate() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "live-translate" })
    }

    func testIncludesESP32BLE() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "esp32-ble" })
    }

    func testIncludesAppAttest() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "app-attest" })
    }

    func testIncludesLaya() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "laya" })
    }

    func testIncludesArmyList() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "army-list" })
    }

    func testIncludesBlather() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "blather" })
    }
}
