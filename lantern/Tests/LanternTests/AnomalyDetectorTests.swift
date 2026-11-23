import XCTest
@testable import Lantern

final class AnomalyDetectorTests: XCTestCase {
    private let homeNetwork = NetworkIdentity(
        id: "gw:04:18:d6:aa:bb:cc",
        ssid: "HomeWiFi",
        gatewayIP: "192.168.1.1",
        gatewayMAC: "04:18:d6:aa:bb:cc",
        localIP: "192.168.1.10",
        interfaceName: "en0",
        subnetPrefix: "192.168.1"
    )

    private func healthyConnectivity(dns: [String] = ["192.168.1.1"]) -> ConnectivityHealth {
        ConnectivityHealth(
            isPathSatisfied: true,
            defaultInterface: "en0",
            defaultGateway: "192.168.1.1",
            isVPNActive: false,
            vpnInterfaces: [],
            dnsServers: dns,
            proxyEnabled: false,
            proxySummary: nil,
            suspiciousHostsEntries: [],
            dnsResolves: true,
            httpProbeOK: true,
            captivePortalSuspected: false,
            checkedAt: Date()
        )
    }

    private func makeDevice(
        mac: String,
        ip: String,
        openPorts: [OpenPort] = [],
        isGateway: Bool = false,
        isThisMac: Bool = false
    ) -> LANDevice {
        LANDevice(
            id: mac,
            macAddress: mac,
            ipAddress: ip,
            hostname: nil,
            vendor: OUILookup.vendor(for: mac),
            mdnsServices: [],
            openPorts: openPorts,
            isGateway: isGateway,
            isThisMac: isThisMac,
            firstSeen: Date(),
            lastSeen: Date(),
            isTrusted: isGateway || isThisMac,
            customLabel: nil,
            classification: nil
        )
    }

    func testFirstPassLearnsBaselineWithoutNewDeviceSpamThenAlertsOnNewHost() {
        let initialBaseline = NetworkBaseline(
            networkID: homeNetwork.id,
            displayName: "HomeWiFi",
            trust: .trusted
        )
        let router = makeDevice(mac: "04:18:d6:aa:bb:cc", ip: "192.168.1.1", isGateway: true)
        let mac = makeDevice(mac: "a4:83:e7:00:00:01", ip: "192.168.1.10", isThisMac: true)

        let snap1 = WatchSnapshot(
            capturedAt: Date(),
            network: homeNetwork,
            devices: [router, mac],
            upnpMappings: [],
            hostProcesses: [],
            connectivity: healthyConnectivity(),
            externalVantage: nil
        )
        let res1 = AnomalyDetector.evaluate(snapshot: snap1, baseline: initialBaseline, muteRules: [])
        XCTAssertTrue(res1.emittedFindings.isEmpty)

        // Second pass: an unknown device with ADB port 5555 appears.
        let androidBox = makeDevice(
            mac: "00:e0:4c:11:22:33",
            ip: "192.168.1.77",
            openPorts: [OpenPort(port: 5555, serviceName: "Android ADB", isSuspicious: true)]
        )
        let snap2 = WatchSnapshot(
            capturedAt: Date(),
            network: homeNetwork,
            devices: [router, mac, androidBox],
            upnpMappings: [],
            hostProcesses: [],
            connectivity: healthyConnectivity(),
            externalVantage: nil
        )
        let res2 = AnomalyDetector.evaluate(snapshot: snap2, baseline: res1.updatedBaseline, muteRules: [])
        let kinds = Set(res2.emittedFindings.map(\.kind))
        XCTAssertTrue(kinds.contains(.newDevice))
        XCTAssertTrue(kinds.contains(.suspiciousOpenPort))
    }

    func testGatewayMACChangeEmitsCriticalAlert() {
        var baseline = NetworkBaseline(networkID: homeNetwork.id, displayName: "HomeWiFi", trust: .trusted)
        baseline.gatewayMAC = "04:18:d6:aa:bb:cc"

        var spoofedNet = homeNetwork
        spoofedNet.gatewayMAC = "de:ad:be:ef:00:01"

        let snap = WatchSnapshot(
            capturedAt: Date(),
            network: spoofedNet,
            devices: [],
            upnpMappings: [],
            hostProcesses: [],
            connectivity: healthyConnectivity(),
            externalVantage: nil
        )
        let res = AnomalyDetector.evaluate(snapshot: snap, baseline: baseline, muteRules: [])
        let gwFinding = res.emittedFindings.first { $0.kind == .gatewayMACChanged }
        XCTAssertEqual(gwFinding?.severity, .critical)
    }

    func testResidentialProxyHostProcessFanOutAndUploadRatio() {
        var baseline = NetworkBaseline(networkID: homeNetwork.id, displayName: "HomeWiFi", trust: .trusted)
        baseline.gatewayMAC = homeNetwork.gatewayMAC

        let proxyProc = ProcessNetworkSnapshot(
            pid: 999,
            processName: "earn-daemon",
            uniqueRemoteIPs: 28,
            uniqueRemoteSubnets: 14,
            establishedConnections: 20,
            bytesIn: 2_000_000,
            bytesOut: 18_000_000,
            listeningWildcardPorts: [1080],
            sampleRemoteEndpoints: ["1.2.3.4:443", "5.6.7.8:443"]
        )
        let browser = ProcessNetworkSnapshot(
            pid: 100,
            processName: "Safari",
            uniqueRemoteIPs: 40,
            uniqueRemoteSubnets: 25,
            establishedConnections: 30,
            bytesIn: 50_000_000,
            bytesOut: 2_000_000,
            listeningWildcardPorts: [],
            sampleRemoteEndpoints: []
        )

        let snap = WatchSnapshot(
            capturedAt: Date(),
            network: homeNetwork,
            devices: [],
            upnpMappings: [],
            hostProcesses: [proxyProc, browser],
            connectivity: healthyConnectivity(),
            externalVantage: nil
        )
        let res = AnomalyDetector.evaluate(snapshot: snap, baseline: baseline, muteRules: [])
        XCTAssertTrue(res.emittedFindings.contains { $0.kind == .hostProcessHighFanOut && $0.subjectID == "earn-daemon" && $0.severity == .critical })
        XCTAssertTrue(res.emittedFindings.contains { $0.kind == .hostProcessWildcardListener && $0.subjectID == "earn-daemon" })
        // Safari should be ignored by default
        XCTAssertFalse(res.emittedFindings.contains { $0.subjectID == "Safari" })
    }

    func testUntrustedPublicNetworkSuppressesLANNoise() {
        var baseline = NetworkBaseline(networkID: homeNetwork.id, displayName: "CafeWiFi", trust: .untrusted)
        baseline.gatewayMAC = homeNetwork.gatewayMAC

        let stranger = makeDevice(
            mac: "11:22:33:44:55:66",
            ip: "192.168.1.99",
            openPorts: [OpenPort(port: 8080, serviceName: "HTTP Proxy", isSuspicious: true)]
        )
        let snap = WatchSnapshot(
            capturedAt: Date(),
            network: homeNetwork,
            devices: [stranger],
            upnpMappings: [
                UPnPMapping(
                    externalPort: 5555,
                    internalPort: 5555,
                    internalClient: "192.168.1.99",
                    protocolName: "TCP",
                    description: "test",
                    enabled: true,
                    leaseDuration: 0
                ),
            ],
            hostProcesses: [],
            connectivity: healthyConnectivity(),
            externalVantage: nil
        )
        let res = AnomalyDetector.evaluate(snapshot: snap, baseline: baseline, muteRules: [])
        XCTAssertTrue(res.emittedFindings.isEmpty)
    }

    func testMuteRuleSuppressesFinding() {
        var baseline = NetworkBaseline(networkID: homeNetwork.id, displayName: "HomeWiFi", trust: .trusted)
        baseline.gatewayMAC = homeNetwork.gatewayMAC

        let mute = MuteRule(
            networkID: homeNetwork.id,
            dedupeKey: "upnp:TCP:5555->192.168.1.42:5555",
            label: "Muted UPnP"
        )
        let snap = WatchSnapshot(
            capturedAt: Date(),
            network: homeNetwork,
            devices: [],
            upnpMappings: [
                UPnPMapping(
                    externalPort: 5555,
                    internalPort: 5555,
                    internalClient: "192.168.1.42",
                    protocolName: "TCP",
                    description: "adb",
                    enabled: true,
                    leaseDuration: 0
                ),
            ],
            hostProcesses: [],
            connectivity: healthyConnectivity(),
            externalVantage: nil
        )
        let res = AnomalyDetector.evaluate(snapshot: snap, baseline: baseline, muteRules: [mute])
        XCTAssertTrue(res.emittedFindings.isEmpty)
    }
}
