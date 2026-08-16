import XCTest
@testable import Onramp

final class ConnectivityAnalyzerTests: XCTestCase {
    func testHealthySnapshotProducesEmptySteps() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = true
        snap.pathStatusLabel = "satisfied"
        snap.hasDefaultRoute = true
        snap.defaultInterface = "en0"
        snap.defaultGateway = "192.168.1.1"
        snap.dnsResolvers = ["1.1.1.1"]
        snap.dnsLookupOk = true
        snap.tcpCloudflareOk = true
        snap.httpExampleOk = true
        snap.httpExampleStatus = 200
        snap.captiveLikely = false

        let report = ConnectivityAnalyzer.analyze(snap, kind: .cantGetOnline)
        XCTAssertTrue(report.headline.localizedCaseInsensitiveContains("OK"))
        XCTAssertTrue(report.actionableSteps.isEmpty)
        XCTAssertTrue(report.evidence.contains { $0.contains("path_status") })
    }

    func testUnsatisfiedPathRanksHighest() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = false
        snap.pathStatusLabel = "unsatisfied"
        snap.hasDefaultRoute = false
        snap.dnsResolvers = []
        snap.dnsLookupOk = false
        snap.tcpCloudflareOk = false
        snap.httpExampleOk = false

        let findings = ConnectivityAnalyzer.collectFindings(snap)
        XCTAssertEqual(findings.first?.code, .noPath)
        let report = ConnectivityAnalyzer.analyze(snap, kind: .cantGetOnline)
        XCTAssertTrue(report.headline.localizedCaseInsensitiveContains("path"))
        XCTAssertFalse(report.actionableSteps.isEmpty)
        XCTAssertTrue(report.actionableSteps.contains { $0.contains("Network") })
    }

    func testDnsFailTcpOkLooksLikeDns() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = true
        snap.pathStatusLabel = "satisfied"
        snap.hasDefaultRoute = true
        snap.defaultInterface = "en0"
        snap.dnsResolvers = ["127.0.0.1"]
        snap.dnsLookupOk = false
        snap.tcpCloudflareOk = true
        snap.httpExampleOk = false

        let findings = ConnectivityAnalyzer.collectFindings(snap)
        let codes = findings.map(\.code)
        XCTAssertTrue(codes.contains(.dnsLocalhost))
        XCTAssertTrue(codes.contains(.dnsLookupFailed))
        let report = ConnectivityAnalyzer.analyze(snap, kind: .dnsWrong)
        XCTAssertTrue(
            report.headline.localizedCaseInsensitiveContains("DNS")
                || report.likelyCause.localizedCaseInsensitiveContains("DNS")
                || report.likelyCause.localizedCaseInsensitiveContains("localhost")
        )
    }

    func testVpnPlaybookBoostsVpnFinding() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = true
        snap.hasDefaultRoute = true
        snap.defaultInterface = "utun3"
        snap.defaultIsVpn = true
        snap.pathUsesVpn = true
        snap.vpnLikeInterfaces = ["utun3"]
        snap.dnsResolvers = ["10.0.0.1"]
        snap.dnsLookupOk = false
        snap.tcpCloudflareOk = false
        snap.httpExampleOk = false

        let report = ConnectivityAnalyzer.analyze(snap, kind: .vpnBroken)
        XCTAssertTrue(report.headline.localizedCaseInsensitiveContains("VPN"))
        XCTAssertTrue(report.actionableSteps.contains { $0.localizedCaseInsensitiveContains("VPN") })
    }

    func testCaptivePortalFinding() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = true
        snap.hasDefaultRoute = true
        snap.defaultInterface = "en0"
        snap.dnsResolvers = ["192.168.1.1"]
        snap.dnsLookupOk = true
        snap.tcpCloudflareOk = true
        snap.httpExampleOk = false
        snap.captiveLikely = true
        snap.captiveStatus = 302
        snap.captiveFinalURL = "https://login.hotel.example/portal"

        let report = ConnectivityAnalyzer.analyze(snap, kind: .captivePortal)
        XCTAssertTrue(report.headline.localizedCaseInsensitiveContains("captive"))
        XCTAssertTrue(
            report.actionableSteps.contains { $0.localizedCaseInsensitiveContains("captive.apple.com") }
        )
    }

    func testProxyEnabledSurfacesWhenProbesFail() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = true
        snap.hasDefaultRoute = true
        snap.defaultInterface = "en0"
        snap.dnsResolvers = ["8.8.8.8"]
        snap.proxyEnabledServices = ["Wi-Fi"]
        snap.dnsLookupOk = false
        snap.tcpCloudflareOk = false
        snap.httpExampleOk = false

        let report = ConnectivityAnalyzer.analyze(snap, kind: .cantGetOnline)
        let findings = ConnectivityAnalyzer.collectFindings(snap)
        XCTAssertTrue(findings.contains { $0.code == .proxyBlocking })
        XCTAssertTrue(
            report.actionableSteps.contains { $0.localizedCaseInsensitiveContains("Proxies") }
        )
    }
}

final class ConnectivityPlaybookParseTests: XCTestCase {
    func testApplyPathAndRoute() {
        var snap = ConnectivitySnapshot()
        ConnectivityPlaybookRunner.applyPath(
            """
            Status: satisfied
            Expensive: no
            Interfaces: en0, utun2
            """,
            into: &snap
        )
        XCTAssertEqual(snap.pathSatisfied, true)
        XCTAssertEqual(snap.pathInterfaces, ["en0", "utun2"])

        ConnectivityPlaybookRunner.applyRoute(
            """
            destination: default
            gateway: 192.168.1.1
            interface: en0
            """,
            into: &snap
        )
        XCTAssertEqual(snap.defaultInterface, "en0")
        XCTAssertEqual(snap.defaultGateway, "192.168.1.1")
        XCTAssertEqual(snap.hasDefaultRoute, true)
        XCTAssertFalse(snap.defaultIsVpn)
    }

    func testDnsLookupSucceeded() {
        let ok = """
        A:
        93.184.216.34

        AAAA:
        (none)
        """
        XCTAssertTrue(ConnectivityPlaybookRunner.dnsLookupSucceeded(ok))
        let bad = """
        A:
        (none)

        AAAA:
        (none)
        """
        XCTAssertFalse(ConnectivityPlaybookRunner.dnsLookupSucceeded(bad))
    }

    func testCaptiveRedirectDetected() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = true
        let report = DiagnosticReport(
            title: "HTTP probe",
            body: """
            Status: 200
            Final URL: https://wifi.hotel.example/login
            Bytes: 1200
            Time: 80 ms
            """,
            proposedFixes: []
        )
        ConnectivityPlaybookRunner.applyCaptive(report, into: &snap)
        XCTAssertTrue(snap.captiveLikely)
        XCTAssertEqual(snap.captiveFinalURL, "https://wifi.hotel.example/login")
    }

    func testScenarioChipsAreNetworkOnly() {
        let titles = TriageChatModel.scenarioPrompts.map(\.title)
        XCTAssertTrue(titles.contains("Can't get online"))
        XCTAssertFalse(titles.contains { $0.localizedCaseInsensitiveContains("memory") })
        XCTAssertFalse(titles.contains { $0.localizedCaseInsensitiveContains("disk") })
    }

    func testToolboxNetworkCasesLeading() {
        XCTAssertEqual(ToolboxCheck.networkCases.first, .pathStatus)
        XCTAssertTrue(ToolboxCheck.networkCases.contains(.dnsConfig))
        XCTAssertFalse(ToolboxCheck.networkCases.contains(.topCPU))
        XCTAssertTrue(ToolboxCheck.advancedCases.contains(.topCPU))
    }
}
