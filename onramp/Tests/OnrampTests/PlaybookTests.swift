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

        let report = ConnectivityAnalyzer.analyze(snap, kind: .cantGetOnline).report
        XCTAssertTrue(report.headline.localizedCaseInsensitiveContains("online")
            || report.headline.localizedCaseInsensitiveContains("OK"))
        XCTAssertTrue(report.looksHealthy)
        XCTAssertEqual(report.causeSectionTitle, "What we found")
        XCTAssertTrue(report.markdown.contains("What we found"))
        XCTAssertFalse(report.markdown.contains("Likely cause"))
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
        let outcome = ConnectivityAnalyzer.analyze(snap, kind: .cantGetOnline)
        XCTAssertTrue(outcome.report.headline.localizedCaseInsensitiveContains("path"))
        XCTAssertFalse(outcome.report.actionableSteps.isEmpty)
        XCTAssertTrue(outcome.report.actionableSteps.contains { $0.contains("Network") })
        XCTAssertTrue(outcome.actions.contains { $0.id == "open-network" })
        XCTAssertFalse(outcome.looksOnline)
        XCTAssertFalse(outcome.report.looksHealthy)
        XCTAssertEqual(outcome.report.causeSectionTitle, "Likely cause")
        XCTAssertTrue(outcome.report.markdown.contains("Likely cause"))
        XCTAssertFalse(outcome.report.markdown.contains("What we found"))
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
        let report = ConnectivityAnalyzer.analyze(snap, kind: .dnsWrong).report
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

        let outcome = ConnectivityAnalyzer.analyze(snap, kind: .vpnBroken)
        XCTAssertTrue(outcome.report.headline.localizedCaseInsensitiveContains("VPN"))
        XCTAssertTrue(outcome.report.actionableSteps.contains { $0.localizedCaseInsensitiveContains("VPN") })
        XCTAssertTrue(outcome.actions.contains { $0.id == "recheck-vpn" })
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

        let outcome = ConnectivityAnalyzer.analyze(snap, kind: .captivePortal)
        XCTAssertTrue(outcome.report.headline.localizedCaseInsensitiveContains("captive"))
        XCTAssertTrue(
            outcome.report.actionableSteps.contains { $0.localizedCaseInsensitiveContains("captive.apple.com") }
        )
        XCTAssertTrue(outcome.actions.contains { $0.id == "open-captive" })
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

        let outcome = ConnectivityAnalyzer.analyze(snap, kind: .cantGetOnline)
        let findings = ConnectivityAnalyzer.collectFindings(snap)
        XCTAssertTrue(findings.contains { $0.code == .proxyBlocking })
        XCTAssertTrue(
            outcome.report.actionableSteps.contains { $0.localizedCaseInsensitiveContains("Proxies") }
        )
        XCTAssertTrue(outcome.actions.contains { $0.id == "open-proxies" })
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

    func testSuggestedActionsIncludeRecheck() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = false
        snap.pathStatusLabel = "unsatisfied"
        snap.hasDefaultRoute = false
        let actions = SuggestedActionBuilder.actions(
            for: ConnectivityAnalyzer.collectFindings(snap),
            snapshot: snap,
            kind: .cantGetOnline
        )
        XCTAssertTrue(actions.contains { $0.id == "open-network" })
        XCTAssertTrue(actions.contains { $0.id == "recheck-full" })
        XCTAssertTrue(actions.allSatisfy(\.isReadOnly))
    }

    func testProbeCommandSummariesAreNonEmpty() {
        for probe in SuggestedAction.DiagnosticProbe.allCases {
            XCTAssertFalse(probe.commandSummary.isEmpty)
        }
    }

    func testAdminExtraStepsAppendWhenUnhealthy() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = false
        snap.pathStatusLabel = "unsatisfied"
        snap.hasDefaultRoute = false
        snap.dnsLookupOk = false
        snap.tcpCloudflareOk = false
        snap.httpExampleOk = false
        let outcome = ConnectivityAnalyzer.analyze(
            snap,
            kind: .vpnBroken,
            extraSteps: ["Connect to Corp VPN from the menu bar, then re-run."]
        )
        XCTAssertTrue(
            outcome.report.actionableSteps.contains {
                $0.contains("Corp VPN")
            }
        )
    }

    func testAdminExtraStepsOmittedWhenHealthy() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = true
        snap.hasDefaultRoute = true
        snap.dnsResolvers = ["1.1.1.1"]
        snap.dnsLookupOk = true
        snap.tcpCloudflareOk = true
        snap.httpExampleOk = true
        snap.captiveLikely = false
        let outcome = ConnectivityAnalyzer.analyze(
            snap,
            kind: .cantGetOnline,
            extraSteps: ["Connect to Corp VPN from the menu bar, then re-run."]
        )
        XCTAssertTrue(outcome.looksOnline)
        XCTAssertTrue(outcome.report.actionableSteps.isEmpty)
        XCTAssertFalse(outcome.report.actionableSteps.contains { $0.contains("Corp VPN") })
    }

    func testCustomProbeTargetsAppearInEvidence() {
        var snap = ConnectivitySnapshot()
        snap.pathSatisfied = true
        snap.pathStatusLabel = "satisfied"
        snap.hasDefaultRoute = true
        snap.dnsLookupOk = false
        snap.tcpCloudflareOk = false
        snap.httpExampleOk = false
        snap.probeDnsHost = "intranet.example.com"
        snap.probeHttpURL = "https://intranet.example.com/health"
        snap.probeReachHost = "10.1.0.10"
        snap.probeReachPort = 443
        let evidence = ConnectivityAnalyzer.evidenceBullets(
            snapshot: snap,
            findings: ConnectivityAnalyzer.collectFindings(snap)
        )
        XCTAssertTrue(evidence.contains { $0.contains("intranet.example.com") })
        XCTAssertTrue(evidence.contains { $0.contains("10.1.0.10:443") })
    }
}

final class PlaybookCatalogTests: XCTestCase {
    func testParsesManagedPlistEntry() {
        let entry: [String: Any] = [
            "id": "corp-intranet",
            "title": "Can't reach intranet",
            "subtitle": "VPN + internal DNS/HTTP",
            "symbol": "building.columns",
            "focus": "vpn",
            "dnsHostname": "intranet.example.com",
            "httpURL": "https://intranet.example.com/health",
            "reachHost": "10.1.0.10",
            "reachPort": 443,
            "extraSteps": ["Connect to Corp VPN, then re-run."],
        ]
        guard let parsed = PlaybookDefinitionParser.parseEntry(entry, source: .managed) else {
            return XCTFail("expected a playbook")
        }
        XCTAssertEqual(parsed.id, "corp-intranet")
        XCTAssertEqual(parsed.focus, .vpnBroken)
        XCTAssertEqual(parsed.probes.dnsHostname, "intranet.example.com")
        XCTAssertEqual(parsed.probes.httpURL, "https://intranet.example.com/health")
        XCTAssertEqual(parsed.probes.reachHost, "10.1.0.10")
        XCTAssertEqual(parsed.probes.reachPort, 443)
        XCTAssertEqual(parsed.extraSteps, ["Connect to Corp VPN, then re-run."])
        XCTAssertEqual(parsed.source, .managed)
    }

    func testParsesJSONArrayAndWrapper() {
        let json = """
        {
          "Playbooks": [
            {"id": "corp-dns", "title": "Corp DNS", "focus": "dns"}
          ],
          "DisabledPlaybookIDs": ["captivePortal"]
        }
        """
        let parsed = PlaybookDefinitionParser.parseJSONString(json, source: .managed)
        XCTAssertEqual(parsed.playbooks.map(\.id), ["corp-dns"])
        XCTAssertEqual(parsed.playbooks.first?.focus, .dnsWrong)
        XCTAssertEqual(parsed.disabledIDs, ["captivePortal"])
    }

    func testRejectsUnsafeOrInvalidEntries() {
        let fileURL = PlaybookDefinitionParser.parseEntry(
            ["id": "ok", "title": "Safe title", "httpURL": "file:///etc/hosts"],
            source: .managed
        )
        XCTAssertEqual(fileURL?.probes.httpURL, PlaybookProbes.defaults.httpURL)

        XCTAssertNil(
            PlaybookDefinitionParser.parseEntry(
                ["id": "has spaces", "title": "Nope"],
                source: .managed
            )
        )
        XCTAssertNil(
            PlaybookDefinitionParser.parseEntry(
                ["id": "ok", "title": ""],
                source: .managed
            )
        )
        XCTAssertNil(PlaybookDefinitionParser.parseHTTPURL("javascript:alert(1)"))
        XCTAssertNil(PlaybookDefinitionParser.parseHTTPURL("https://user:pass@example.com/"))
        XCTAssertNil(PlaybookDefinitionParser.parseHTTPURL("/etc/hosts"))
        XCTAssertNotNil(PlaybookDefinitionParser.parseHTTPURL("https://intranet.example.com/health"))
        XCTAssertNil(PlaybookDefinitionParser.sanitizeID("rm -rf"))
        XCTAssertNil(PlaybookDefinitionParser.parsePort(0))
        XCTAssertNil(PlaybookDefinitionParser.parsePort(70000))
        XCTAssertEqual(PlaybookDefinitionParser.parsePort(443), 443)
    }

    func testAssembleMergesManagedOverLocalAndHidesDisabled() {
        let local = PlaybookDefinition(
            id: "corp-intranet",
            title: "Local intranet",
            subtitle: "from file",
            symbolName: "building.columns",
            focus: .vpnBroken,
            source: .localFile,
            probes: .defaults,
            extraSteps: []
        )
        let managed = PlaybookDefinition(
            id: "corp-intranet",
            title: "Managed intranet",
            subtitle: "from MDM",
            symbolName: "building.columns",
            focus: .vpnBroken,
            source: .managed,
            probes: .defaults,
            extraSteps: []
        )
        let extra = PlaybookDefinition(
            id: "wifi-guest",
            title: "Guest Wi‑Fi",
            subtitle: "captive",
            symbolName: "building.2",
            focus: .captivePortal,
            source: .localFile,
            probes: .defaults,
            extraSteps: []
        )
        let catalog = PlaybookCatalog.assemble(
            managed: [managed],
            local: [local, extra],
            disabledIDs: ["captivePortal", "someSitesFail"]
        )
        let ids = catalog.map(\.id)
        XCTAssertTrue(ids.contains(ConnectivityPlaybookKind.cantGetOnline.rawValue))
        XCTAssertFalse(ids.contains(ConnectivityPlaybookKind.captivePortal.rawValue))
        XCTAssertFalse(ids.contains(ConnectivityPlaybookKind.someSitesFail.rawValue))
        XCTAssertEqual(catalog.filter { $0.id == "corp-intranet" }.map(\.title), ["Managed intranet"])
        XCTAssertTrue(ids.contains("wifi-guest"))
    }

    func testAssembleSkipsReservedBuiltInIDs() {
        let spoof = PlaybookDefinition(
            id: ConnectivityPlaybookKind.cantGetOnline.rawValue,
            title: "Evil",
            subtitle: "",
            symbolName: "xmark",
            focus: .cantGetOnline,
            source: .managed,
            probes: .defaults,
            extraSteps: []
        )
        let catalog = PlaybookCatalog.assemble(managed: [spoof], local: [], disabledIDs: [])
        XCTAssertEqual(catalog.filter { $0.id == spoof.id }.count, 1)
        XCTAssertEqual(catalog.first?.title, ConnectivityPlaybookKind.cantGetOnline.title)
        XCTAssertTrue(catalog.first?.isBuiltIn == true)
    }

    func testAssembleKeepsCantGetOnlineIfAllBuiltInsDisabled() {
        let disabled = Set(ConnectivityPlaybookKind.allCases.map(\.rawValue))
        let catalog = PlaybookCatalog.assemble(managed: [], local: [], disabledIDs: disabled)
        XCTAssertEqual(catalog.map(\.id), [ConnectivityPlaybookKind.cantGetOnline.rawValue])
    }

    func testLoadFromUserDefaultsAndJSONFile() throws {
        let suiteName = "onramp.playbook.tests.\(UUID().uuidString)"
        guard let defaults = UserDefaults(suiteName: suiteName) else {
            return XCTFail("suite")
        }
        defaults.removePersistentDomain(forName: suiteName)
        defaults.set(
            [[
                "id": "from-defaults",
                "title": "From defaults",
                "focus": "dns",
            ]],
            forKey: PlaybookPreferenceKey.playbooks
        )
        defaults.set(["vpnBroken"], forKey: PlaybookPreferenceKey.disabledPlaybookIDs)

        let json = """
        [{"id":"from-file","title":"From file","focus":"captive"}]
        """
        let dir = FileManager.default.temporaryDirectory
            .appendingPathComponent("onramp-playbook-\(UUID().uuidString)", isDirectory: true)
        try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        let file = dir.appendingPathComponent("playbooks.json")
        try Data(json.utf8).write(to: file)

        let catalog = PlaybookCatalog.load(defaults: defaults, fileURLs: [file])
        let ids = catalog.map(\.id)
        XCTAssertTrue(ids.contains("from-defaults"))
        XCTAssertTrue(ids.contains("from-file"))
        XCTAssertFalse(ids.contains(ConnectivityPlaybookKind.vpnBroken.rawValue))

        defaults.removePersistentDomain(forName: suiteName)
        try? FileManager.default.removeItem(at: dir)
    }

    func testExampleJSONParses() throws {
        let examples = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .deletingLastPathComponent()
            .deletingLastPathComponent()
            .appendingPathComponent("examples")
        let jsonURL = examples.appendingPathComponent("playbooks.json")
        let json = PlaybookDefinitionParser.parseFile(try Data(contentsOf: jsonURL), url: jsonURL)
        XCTAssertEqual(json.playbooks.first?.id, "corp-intranet")
        XCTAssertEqual(json.playbooks.first?.focus, .vpnBroken)
        XCTAssertEqual(json.disabledIDs, ["captivePortal"])

        let plistURL = examples.appendingPathComponent("playbooks.plist")
        let plist = PlaybookDefinitionParser.parseFile(try Data(contentsOf: plistURL), url: plistURL)
        XCTAssertEqual(plist.playbooks.first?.id, "corp-intranet")
        XCTAssertEqual(plist.playbooks.first?.probes.reachPort, 443)
    }
}
