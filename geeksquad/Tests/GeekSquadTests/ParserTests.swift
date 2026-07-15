import XCTest
@testable import GeekSquad

final class DnsConfigParserTests: XCTestCase {
    func testParsesResolversAndSearch() {
        let text = """
        resolver #1
          nameserver[0] : 1.1.1.1
          nameserver[1] : 1.0.0.1
          search domain[0] : home.arpa
          flags    : Request A records

        resolver #2
          domain   : local
          options  : mdns
        """
        let summary = DnsConfigParser.parse(text)
        XCTAssertEqual(summary.resolvers, ["1.1.1.1", "1.0.0.1"])
        XCTAssertEqual(summary.searchDomains, ["home.arpa"])
        XCTAssertEqual(summary.scopedResolverCount, 2)
        XCTAssertTrue(summary.description.contains("1.1.1.1"))
    }

    func testEmptyInput() {
        let summary = DnsConfigParser.parse("")
        XCTAssertTrue(summary.resolvers.isEmpty)
        XCTAssertEqual(summary.scopedResolverCount, 0)
    }
}

final class HostsFileParserTests: XCTestCase {
    func testParsesAndFlagsSurprises() {
        let text = """
        ##
        # Host Database
        127.0.0.1	localhost
        255.255.255.255	broadcasthost
        ::1             localhost
        127.0.0.1	broken.example.com
        10.0.0.5	intranet.corp
        """
        let summary = HostsFileParser.parse(text)
        XCTAssertGreaterThanOrEqual(summary.entries.count, 4)
        XCTAssertTrue(summary.surprising.contains { $0.names.contains("broken.example.com") })
        XCTAssertTrue(summary.surprising.contains { $0.names.contains("intranet.corp") })
        // Default localhost-only loopback lines should not be "surprising".
        let localhostOnly = summary.surprising.contains { entry in
            guard entry.address == "127.0.0.1" else { return false }
            let names = entry.names.map { $0.lowercased() }
            return names == ["localhost"]
        }
        XCTAssertFalse(localhostOnly)
    }
}

final class ProposedFixesTests: XCTestCase {
    func testDnsEmptyAndLoopback() {
        XCTAssertFalse(ProposedFixes.forDnsConfig(resolvers: []).isEmpty)
        XCTAssertTrue(
            ProposedFixes.forDnsConfig(resolvers: ["127.0.0.1"])
                .joined()
                .localizedCaseInsensitiveContains("localhost")
        )
    }

    func testVpnDefaultRoute() {
        let fixes = ProposedFixes.forDefaultRoute(interface: "utun3", gateway: "10.0.0.1", isVpn: true)
        XCTAssertTrue(fixes.joined().localizedCaseInsensitiveContains("VPN"))
    }

    func testProxyEnabled() {
        XCTAssertFalse(ProposedFixes.forProxyEnabled(services: ["Wi-Fi"]).isEmpty)
        XCTAssertTrue(ProposedFixes.forProxyEnabled(services: []).isEmpty)
    }
}

final class DiagnosticReportTests: XCTestCase {
    func testMarkdownIncludesFixes() {
        let report = DiagnosticReport(
            title: "DNS config",
            body: "Resolvers:\n  - 1.1.1.1",
            proposedFixes: ["Check DNS settings."]
        )
        XCTAssertTrue(report.markdown.contains("## DNS config"))
        XCTAssertTrue(report.markdown.contains("Proposed fixes"))
        XCTAssertTrue(report.markdown.contains("Check DNS settings."))
    }
}
