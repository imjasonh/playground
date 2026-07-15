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

    func testCompactMarkdownTruncates() {
        let body = String(repeating: "x", count: 2_500)
        let report = DiagnosticReport(title: "Big", body: body, proposedFixes: [])
        let compact = report.compactMarkdown(maxCharacters: 100)
        XCTAssertLessThanOrEqual(compact.count, 120)
        XCTAssertTrue(compact.contains("…(truncated)"))
    }
}

final class ProcessListParserTests: XCTestCase {
    func testParsesPsRowsAndMatchesQuery() {
        let text = """
          123  512000  12.5 /Applications/Cursor.app/Contents/MacOS/Cursor
          124   10240   0.1 /Applications/Cursor.app/Contents/Frameworks/Cursor Helper.app/Contents/MacOS/Cursor Helper
          200    4096   0.0 /System/Library/CoreServices/Finder.app/Contents/MacOS/Finder
        """
        let rows = ProcessListParser.parse(text)
        XCTAssertEqual(rows.count, 3)
        XCTAssertEqual(rows[0].pid, 123)
        XCTAssertEqual(rows[0].rssKilobytes, 512_000)
        XCTAssertEqual(rows[0].cpuPercent, 12.5, accuracy: 0.01)

        let matches = ProcessListParser.matching(rows, query: "Cursor")
        XCTAssertEqual(matches.count, 2)

        let summary = ProcessListParser.summarize(
            matches: matches,
            query: "Cursor",
            physicalMemoryBytes: 16 * 1_073_741_824
        )
        XCTAssertTrue(summary.body.contains("Matching processes: 2"))
        XCTAssertTrue(summary.body.contains("Total memory"))
        XCTAssertFalse(summary.proposedFixes.isEmpty)
    }

    func testNoMatches() {
        let summary = ProcessListParser.summarize(
            matches: [],
            query: "NopeApp",
            physicalMemoryBytes: 8 * 1_073_741_824
        )
        XCTAssertTrue(summary.body.contains("No running processes matched"))
    }
}

final class DiskSpaceParserTests: XCTestCase {
    func testParsesDfKP() {
        let text = """
        Filesystem 1024-blocks Used Available Capacity Mounted on
        /dev/disk3s1s1 488245288 400000000 50000000 89% /
        /dev/disk3s5 488245288 100000000 300000000 25% /System/Volumes/Data
        """
        let volumes = DiskSpaceParser.parse(text)
        XCTAssertEqual(volumes.count, 2)
        XCTAssertEqual(volumes[0].mountPoint, "/")
        XCTAssertEqual(volumes[0].capacityPercent, 89)
        let summary = DiskSpaceParser.summarize(volumes)
        XCTAssertTrue(summary.body.contains("/"))
        XCTAssertFalse(summary.proposedFixes.isEmpty)
    }
}

final class VmStatParserTests: XCTestCase {
    func testParsesVmStat() {
        let text = """
        Mach Virtual Memory Statistics: (page size of 16384 bytes)
        Pages free:                               1000.
        Pages active:                             2000.
        Pages inactive:                           3000.
        Pages speculative:                         100.
        Pages wired down:                         4000.
        Pages occupied by compressor:             5000.
        Swapins:                                   10.
        Swapouts:                                  20.
        """
        let stats = VmStatParser.parse(text)
        XCTAssertEqual(stats?.pageSizeBytes, 16_384)
        XCTAssertEqual(stats?.pagesFree, 1000)
        XCTAssertEqual(stats?.pagesWired, 4000)
        XCTAssertEqual(stats?.swapouts, 20)
    }
}

final class ListeningPortsParserTests: XCTestCase {
    func testParsesLsofListen() {
        let text = """
        COMMAND   PID USER   FD   TYPE DEVICE SIZE/OFF NODE NAME
        Cursor    123 me     10u  IPv4 0xabc      0t0  TCP *:3000 (LISTEN)
        postgres  456 me     5u   IPv6 0xdef      0t0  TCP [::1]:5432 (LISTEN)
        """
        let ports = ListeningPortsParser.parse(text)
        XCTAssertEqual(ports.count, 2)
        XCTAssertEqual(ports[0].address, "*:3000")
        let filtered = ListeningPortsParser.summarize(ports, filterPort: 3000)
        XCTAssertTrue(filtered.body.contains("3000"))
        XCTAssertTrue(filtered.body.contains("Cursor"))
    }
}

final class CrashReportsScannerTests: XCTestCase {
    func testSummarizeEmpty() {
        let summary = CrashReportsScanner.summarize([], query: "Cursor")
        XCTAssertTrue(summary.body.contains("No recent crash reports matched"))
    }
}

final class FolderSizeParserTests: XCTestCase {
    func testParsesDuSK() {
        XCTAssertEqual(FolderSizeParser.parseDuSK("12345\t/Users/me/Downloads"), 12_345)
        XCTAssertNil(FolderSizeParser.parseDuSK(""))
    }

    func testSummarizeHighlightsLargeFolders() {
        let samples = [
            FolderSizeSample(name: "Downloads", path: "/tmp/d", kilobytes: 20 * 1_048_576, error: nil),
            FolderSizeSample(name: "Desktop", path: "/tmp/e", kilobytes: 100_000, error: nil),
        ]
        let summary = FolderSizeParser.summarize(samples)
        XCTAssertTrue(summary.body.contains("Downloads"))
        XCTAssertTrue(summary.proposedFixes.contains(where: { $0.contains("Downloads") }))
    }
}

final class LaunchAgentsParserTests: XCTestCase {
    func testSummarizeCounts() {
        let items = [
            LaunchAgentItem(label: "com.example.a", path: "/tmp/a.plist", scope: "user"),
            LaunchAgentItem(label: "com.example.b", path: "/tmp/b.plist", scope: "local"),
        ]
        let summary = LaunchAgentsParser.summarize(items)
        XCTAssertTrue(summary.body.contains("User LaunchAgents: 1"))
        XCTAssertTrue(summary.body.contains("com.example.a"))
    }
}

final class BatteryPowerParserTests: XCTestCase {
    func testParsesPercent() {
        let text = """
        Now drawing from 'Battery Power'
         -InternalBattery-0 (id=123)	42%; discharging; 3:21 remaining present: true
        """
        XCTAssertEqual(BatteryPowerParser.percent(from: text), 42)
    }
}

final class TriageReportViewModelTests: XCTestCase {
    func testMarkdownIncludesSections() {
        let report = TriageReportViewModel(
            headline: "High load",
            likelyCause: "CPU pegged",
            evidence: ["load 5.9"],
            proposedSteps: ["Quit heavy apps"]
        )
        XCTAssertTrue(report.markdown.contains("High load"))
        XCTAssertTrue(report.markdown.contains("Likely cause"))
        XCTAssertTrue(report.markdown.contains("Quit heavy apps"))
    }
}

final class ProcessListParserSpotlightTests: XCTestCase {
    func testDetectsSpotlightHelpers() {
        let row = ProcessRow(
            pid: 1,
            rssKilobytes: 100,
            cpuPercent: 90,
            command: "/System/Library/Frameworks/CoreServices.framework/Versions/A/Frameworks/Metadata.framework/Versions/A/Support/mds_stores"
        )
        XCTAssertTrue(ProcessListParser.isSpotlightRelated(row))
    }
}

final class ActivityMonitorLinksTests: XCTestCase {
    func testLinkifiesBarePhrase() {
        let linked = ActivityMonitorLinks.linkify("Open Activity Monitor and check CPU.")
        XCTAssertTrue(linked.contains("[Activity Monitor](\(ActivityMonitorLinks.markdownURL))"))
        XCTAssertTrue(linked.contains("and check CPU."))
    }

    func testDoesNotDoubleLink() {
        let already = "[Activity Monitor](\(ActivityMonitorLinks.markdownURL))"
        XCTAssertEqual(ActivityMonitorLinks.linkify(already), already)
    }
}
