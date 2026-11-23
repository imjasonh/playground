import XCTest
@testable import Lantern

final class ParserTests: XCTestCase {
    func testOUILookupNormalizesAndIdentifiesVendor() {
        XCTAssertEqual(OUILookup.normalizeMAC("A:B:c:d:e:f"), "0a:0b:0c:0d:0e:0f")
        XCTAssertEqual(OUILookup.normalizeMAC("B8-27-EB-11-22-33"), "b8:27:eb:11:22:33")
        XCTAssertNil(OUILookup.normalizeMAC("not-a-mac"))

        XCTAssertEqual(OUILookup.vendor(for: "b8:27:eb:11:22:33"), "Raspberry Pi")
        XCTAssertEqual(OUILookup.vendor(for: "24:0a:c4:aa:bb:cc"), "Espressif IoT")
        // Locally administered bit (0x02) set in first octet: 0x06
        XCTAssertTrue(OUILookup.isLocallyAdministered("06:11:22:33:44:55"))
        XCTAssertEqual(OUILookup.vendor(for: "06:11:22:33:44:55"), "Private / Randomized MAC")
    }

    func testParseDefaultRoute() {
        let sample = """
           route to: default
        destination: default
               mask: default
            gateway: 192.168.1.1
          interface: en0
              flags: <UP,GATEWAY,DONE,STATIC,PRCLONING,GLOBAL>
        """
        let parsed = NetworkIdentityCollector.parseDefaultRoute(sample)
        XCTAssertEqual(parsed.gateway, "192.168.1.1")
        XCTAssertEqual(parsed.interface, "en0")
        XCTAssertEqual(NetworkIdentityCollector.ipv4Prefix("192.168.1.1"), "192.168.1")
    }

    func testParseARPTableSkipsIncompleteAndNormalizesShortOctets() {
        let sample = """
        router.local (192.168.1.1) at 4:18:d6:aa:bb:cc on en0 ifscope [ethernet]
        ? (192.168.1.25) at (incomplete) on en0 ifscope [ethernet]
        tv-box.local (192.168.1.42) at 00:e0:4c:1:2:3 on en0 ifscope [ethernet]
        ? (224.0.0.251) at 01:00:5e:00:00:fb on en0 ifscope permanent [ethernet]
        """
        let entries = LANDiscoveryCollector.parseARPTable(sample)
        XCTAssertEqual(entries.count, 3)
        XCTAssertEqual(entries[0].macAddress, "04:18:d6:aa:bb:cc")
        XCTAssertEqual(entries[0].hostname, "router.local")
        XCTAssertEqual(entries[1].macAddress, "00:e0:4c:01:02:03")
        XCTAssertTrue(LANDiscoveryCollector.isBroadcastOrMulticastMAC(entries[2].macAddress))
    }

    func testUPnPParsers() {
        let ssdp = """
        HTTP/1.1 200 OK\r
        CACHE-CONTROL: max-age=120\r
        LOCATION: http://192.168.1.1:5000/rootDesc.xml\r
        ST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r
        """
        let locs = UPnPCollector.parseSSDPLocations(ssdp)
        XCTAssertEqual(locs, ["http://192.168.1.1:5000/rootDesc.xml"])

        let descXML = """
        <root><device><serviceList>
          <service>
            <serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType>
            <controlURL>/ctl/IPConn</controlURL>
          </service>
        </serviceList></device></root>
        """
        let baseURL = URL(string: "http://192.168.1.1:5000/rootDesc.xml")!
        let endpoint = UPnPCollector.parseControlEndpoint(xml: descXML, baseURL: baseURL)
        XCTAssertEqual(endpoint?.controlURL.absoluteString, "http://192.168.1.1:5000/ctl/IPConn")
        XCTAssertEqual(endpoint?.serviceType, "urn:schemas-upnp-org:service:WANIPConnection:1")

        let soap = """
        <s:Envelope><s:Body><u:GetGenericPortMappingEntryResponse>
          <NewExternalPort>5555</NewExternalPort>
          <NewProtocol>TCP</NewProtocol>
          <NewInternalPort>5555</NewInternalPort>
          <NewInternalClient>192.168.1.42</NewInternalClient>
          <NewEnabled>1</NewEnabled>
          <NewPortMappingDescription>android-box</NewPortMappingDescription>
          <NewLeaseDuration>0</NewLeaseDuration>
        </u:GetGenericPortMappingEntryResponse></s:Body></s:Envelope>
        """
        let mapping = UPnPCollector.parsePortMappingSOAP(soap)
        XCTAssertEqual(mapping?.externalPort, 5555)
        XCTAssertEqual(mapping?.internalClient, "192.168.1.42")
        XCTAssertEqual(mapping?.description, "android-box")
        XCTAssertEqual(mapping?.enabled, true)
    }

    func testHostTrafficParsers() {
        let nettop = """
        ,bytes_in,bytes_out,
        shadyproxy.4242,1000000,9000000,
        Safari.100,5000000,100000,
        """
        let totals = HostTrafficCollector.parseNettop(nettop)
        XCTAssertEqual(totals[4242]?.bytesIn, 1_000_000)
        XCTAssertEqual(totals[4242]?.bytesOut, 9_000_000)

        let lsof = """
        COMMAND     PID USER   FD   TYPE DEVICE SIZE/OFF NODE NAME
        shadyproxy 4242 user   10u  IPv4 0x1    0t0      TCP 192.168.1.10:50001->1.2.3.4:443 (ESTABLISHED)
        shadyproxy 4242 user   11u  IPv4 0x2    0t0      TCP 192.168.1.10:50002->5.6.7.8:443 (ESTABLISHED)
        shadyproxy 4242 user   12u  IPv4 0x3    0t0      TCP *:1080 (LISTEN)
        shadyproxy 4242 user   13u  IPv4 0x4    0t0      TCP 192.168.1.10:50003->192.168.1.1:53 (ESTABLISHED)
        """
        let snapshots = HostTrafficCollector.parseLsof(lsof, byteTotalsByPID: totals)
        XCTAssertEqual(snapshots.count, 1)
        let proc = snapshots[0]
        XCTAssertEqual(proc.processName, "shadyproxy")
        // Local 192.168.1.1 is excluded from external fan-out
        XCTAssertEqual(proc.uniqueRemoteIPs, 2)
        XCTAssertEqual(proc.uniqueRemoteSubnets, 2)
        XCTAssertEqual(proc.listeningWildcardPorts, [1080])
        XCTAssertEqual(proc.uploadRatio, 0.9, accuracy: 0.001)
    }

    func testConnectivityParsers() {
        let scutil = """
        resolver #1
          nameserver[0] : 192.168.1.1
          nameserver[1] : 1.1.1.1
          nameserver[2] : 192.168.1.1
        """
        XCTAssertEqual(ConnectivityCollector.parseDNSServers(scutil), ["192.168.1.1", "1.1.1.1"])

        let hosts = """
        ##
        127.0.0.1 localhost
        255.255.255.255 broadcasthost
        ::1 localhost
        10.0.0.5 api.example.com # custom
        """
        XCTAssertEqual(ConnectivityCollector.parseSuspiciousHostsEntries(hosts), ["10.0.0.5 api.example.com"])
    }

    func testExternalVantageParsers() {
        XCTAssertTrue(ExternalVantageCollector.matchesProxyBrokerDomain("api.honeygain.com"))
        XCTAssertTrue(ExternalVantageCollector.matchesProxyBrokerDomain("packetstream.io"))
        XCTAssertFalse(ExternalVantageCollector.matchesProxyBrokerDomain("apple.com"))

        let piholeJSON = Data("""
        {"top_sources":{"tv.lan|192.168.1.50":8400,"192.168.1.10":200}}
        """.utf8)
        let pihole = ExternalVantageCollector.parsePiholeTopClients(piholeJSON)
        XCTAssertNil(pihole.errorMessage)
        XCTAssertEqual(pihole.chattyClients.first?.clientIP, "192.168.1.50")
        XCTAssertEqual(pihole.chattyClients.first?.queryCount, 8400)

        let adguardJSON = Data("""
        {"top_clients":[{"192.168.1.99":6200}],"top_queried_domains":[{"sdk.earnapp.com":120}]}
        """.utf8)
        let adguard = ExternalVantageCollector.parseAdGuardStats(adguardJSON)
        XCTAssertEqual(adguard.chattyClients.first?.suspiciousDomains, ["sdk.earnapp.com"])
    }
}
