import XCTest
@testable import Lantern

final class BaselineStoreTests: XCTestCase {
    func testPersistsBaselinesTrustAndMuteRulesAcrossReload() {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent("lantern-tests-\(UUID().uuidString)", isDirectory: true)
        let fileURL = tempDir.appendingPathComponent("state.json")
        defer { try? FileManager.default.removeItem(at: tempDir) }

        let store1 = BaselineStore(fileURL: fileURL)
        let net = NetworkIdentity(
            id: "gw:04:18:d6:aa:bb:cc",
            ssid: "HomeWiFi",
            gatewayIP: "192.168.1.1",
            gatewayMAC: "04:18:d6:aa:bb:cc",
            localIP: "192.168.1.10",
            interfaceName: "en0",
            subnetPrefix: "192.168.1"
        )

        _ = store1.baseline(for: net)
        store1.setTrust(.trusted, for: net.id)

        let finding = Finding(
            dedupeKey: "newDevice:aa:bb:cc:dd:ee:ff",
            networkID: net.id,
            kind: .newDevice,
            severity: .notice,
            title: "New device",
            summary: "Observed new device",
            evidence: []
        )
        store1.mute(finding: finding)

        // Reload from disk in a fresh store instance
        let store2 = BaselineStore(fileURL: fileURL)
        XCTAssertEqual(store2.state.baselines[net.id]?.trust, .trusted)
        XCTAssertTrue(store2.isMuted(networkID: net.id, dedupeKey: finding.dedupeKey))
    }
}
