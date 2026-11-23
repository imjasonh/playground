import XCTest
@testable import Lantern

final class IntelligenceTests: XCTestCase {
    func testDeviceClassifierPromptStaysCompactForSmallContextWindow() {
        let device = LANDevice(
            id: "00:e0:4c:11:22:33",
            macAddress: "00:e0:4c:11:22:33",
            ipAddress: "192.168.1.77",
            hostname: "android-tv.local",
            vendor: "Realtek",
            mdnsServices: ["_googlecast._tcp", "_adb._tcp"],
            openPorts: [OpenPort(port: 5555, serviceName: "Android ADB", isSuspicious: true)],
            isGateway: false,
            isThisMac: false,
            firstSeen: Date(),
            lastSeen: Date(),
            isTrusted: false,
            customLabel: nil,
            classification: nil
        )

        let prompt = DeviceClassifier.makePrompt(for: device)
        // Must stay tiny so it never blows AFM's ~4k token window.
        XCTAssertLessThan(prompt.count, 600)

        let heuristic = DeviceClassifier.heuristicClassify(device)
        XCTAssertEqual(heuristic.category, "TV")
        XCTAssertNotNil(heuristic.riskNote)
        XCTAssertEqual(heuristic.source, .heuristic)
    }

    func testFindingExplainerPromptAndDeterministicFallback() {
        let finding = Finding(
            dedupeKey: "hostFanOut:earn-daemon",
            networkID: "gw:1",
            kind: .hostProcessHighFanOut,
            severity: .critical,
            title: "earn-daemon talking to 28 external IPs",
            summary: "High external IP diversity across 14 /16 subnets.",
            evidence: ["PID 999", "18.0 MB out (90% upload ratio)"]
        )

        let prompt = FindingExplainer.makePrompt(for: finding)
        XCTAssertLessThan(prompt.count, 800)

        let fallback = FindingExplainer.fallback(for: finding)
        XCTAssertFalse(fallback.generatedByAFM)
        XCTAssertEqual(fallback.headline, finding.title)
        XCTAssertFalse(fallback.nextStep.isEmpty)
    }

    func testScopedInvestigatorPromptIsBounded() {
        let finding = Finding(
            dedupeKey: "suspiciousOpenPort:aa:bb:cc:dd:ee:ff:1080",
            networkID: "gw:1",
            kind: .suspiciousOpenPort,
            severity: .warning,
            title: "Device exposes SOCKS Proxy (:1080)",
            summary: "192.168.1.42 has port 1080 open.",
            evidence: ["Open port: 1080/tcp (SOCKS Proxy)"]
        )
        let prompt = ScopedInvestigator.buildScopedPrompt(
            question: "Is this dangerous?",
            finding: finding,
            relatedDevice: nil
        )
        XCTAssertLessThan(prompt.count, 900)
    }
}
