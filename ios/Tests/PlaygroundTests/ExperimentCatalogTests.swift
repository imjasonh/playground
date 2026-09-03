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

    func testIncludesSnoreLog() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "snore-log" })
    }

    func testIncludesZCamera() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "z-camera" })
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

    func testIncludesDoomFace() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "doom-face" })
    }

    func testIncludesNFCTags() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "nfc-tags" })
    }

    func testIncludesDeviceAgent() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "device-agent" })
    }

    func testIncludesArmyList() {
        XCTAssertTrue(ExperimentCatalog.all.contains { $0.id == "army-list" })
    }

    func testDeviceAgentIsListedRightUnderRideMonitor() throws {
        let ids = ExperimentCatalog.all.map(\.id)
        let rideIndex = try XCTUnwrap(ids.firstIndex(of: "ride-monitor"))
        let agentIndex = try XCTUnwrap(ids.firstIndex(of: "device-agent"))
        XCTAssertEqual(agentIndex, rideIndex + 1)
    }
}
