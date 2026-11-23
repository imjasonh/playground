import Darwin
import Foundation
import Network

/// Discovers LAN devices via ARP table, throttled /24 UDP nudge (to populate ARP),
/// and mDNS/Bonjour service browsing.
enum LANDiscoveryCollector {
    struct ARPEntry: Equatable, Sendable {
        var ipAddress: String
        var macAddress: String
        var interfaceName: String?
        var hostname: String?
    }

    /// Runs a lightweight, non-intrusive discovery pass on the current subnet.
    static func discover(
        network: NetworkIdentity,
        existingDevices: [String: LANDevice],
        nudgeSubnet: Bool = true,
        now: Date = Date()
    ) async -> [LANDevice] {
        if nudgeSubnet, let prefix = network.subnetPrefix {
            await nudgeLocalSubnet(prefix: prefix)
        }

        async let mdnsMap = browseMDNSServices(durationSeconds: 1.5)
        let arpOutput = (try? ProcessRunner.run("/usr/sbin/arp", arguments: ["-a"], timeoutSeconds: 5))?.stdout ?? ""
        let arpEntries = parseARPTable(arpOutput)
        let servicesByHost = await mdnsMap

        var byID: [String: LANDevice] = [:]
        for entry in arpEntries {
            // Skip multicast/broadcast MACs
            if isBroadcastOrMulticastMAC(entry.macAddress) { continue }
            // Keep only entries matching our active subnet when known
            if let prefix = network.subnetPrefix, !entry.ipAddress.hasPrefix(prefix + ".") {
                continue
            }

            let mac = entry.macAddress
            let existing = existingDevices[mac]
            let isGateway = (entry.ipAddress == network.gatewayIP) || (mac == network.gatewayMAC)
            let isThisMac = (entry.ipAddress == network.localIP)

            let hostKey = entry.hostname?.lowercased()
            let mdns = hostKey.flatMap { servicesByHost[$0] } ?? existing?.mdnsServices ?? []

            let device = LANDevice(
                id: mac,
                macAddress: mac,
                ipAddress: entry.ipAddress,
                hostname: entry.hostname ?? existing?.hostname,
                vendor: OUILookup.vendor(for: mac) ?? existing?.vendor,
                mdnsServices: Array(Set(mdns)).sorted(),
                openPorts: existing?.openPorts ?? [],
                isGateway: isGateway,
                isThisMac: isThisMac,
                firstSeen: existing?.firstSeen ?? now,
                lastSeen: now,
                isTrusted: existing?.isTrusted ?? (isGateway || isThisMac),
                customLabel: existing?.customLabel,
                classification: existing?.classification
            )
            byID[mac] = device
        }

        return byID.values.sorted { lhs, rhs in
            if lhs.isGateway != rhs.isGateway { return lhs.isGateway }
            if lhs.isThisMac != rhs.isThisMac { return lhs.isThisMac }
            return lhs.ipAddress.localizedStandardCompare(rhs.ipAddress) == .orderedAscending
        }
    }

    // MARK: - Pure parsers (unit-tested)

    /// Parses macOS `arp -a` output:
    /// `router.local (192.168.1.1) at aa:bb:cc:dd:ee:ff on en0 ifscope [ethernet]`
    /// `? (192.168.1.42) at 1:2:3:4:5:6 on en0 ifscope [ethernet]`
    static func parseARPTable(_ stdout: String) -> [ARPEntry] {
        var entries: [ARPEntry] = []
        for rawLine in stdout.split(separator: "\n") {
            let line = rawLine.trimmingCharacters(in: .whitespaces)
            guard let lparen = line.firstIndex(of: "("),
                  let rparen = line.firstIndex(of: ")"),
                  lparen < rparen
            else { continue }

            let hostPart = line[..<lparen].trimmingCharacters(in: .whitespaces)
            let hostname = (hostPart.isEmpty || hostPart == "?") ? nil : hostPart
            let ip = String(line[line.index(after: lparen)..<rparen])

            let afterParen = line[line.index(after: rparen)...]
            let tokens = afterParen.split(separator: " ")
            guard let atIdx = tokens.firstIndex(of: "at"), atIdx + 1 < tokens.count else {
                continue
            }
            let rawMAC = String(tokens[atIdx + 1])
            guard rawMAC != "(incomplete)", let normMAC = OUILookup.normalizeMAC(rawMAC) else {
                continue
            }

            var iface: String?
            if let onIdx = tokens.firstIndex(of: "on"), onIdx + 1 < tokens.count {
                iface = String(tokens[onIdx + 1])
            }

            entries.append(
                ARPEntry(
                    ipAddress: ip,
                    macAddress: normMAC,
                    interfaceName: iface,
                    hostname: hostname
                )
            )
        }
        return entries
    }

    static func isBroadcastOrMulticastMAC(_ mac: String) -> Bool {
        if mac == "ff:ff:ff:ff:ff:ff" { return true }
        if mac.hasPrefix("01:00:5e:") || mac.hasPrefix("33:33:") { return true }
        return false
    }

    // MARK: - Active helpers

    /// Sends a single empty UDP datagram to port 9 (discard) across .1...254 so the OS
    /// resolves ARP entries for live hosts without spawning 254 ping processes.
    private static func nudgeLocalSubnet(prefix: String) async {
        await Task.detached(priority: .utility) {
            let fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP)
            guard fd >= 0 else { return }
            defer { close(fd) }

            var payload: UInt8 = 0
            for host in 1...254 {
                let ip = "\(prefix).\(host)"
                var addr = sockaddr_in()
                addr.sin_len = UInt8(MemoryLayout<sockaddr_in>.size)
                addr.sin_family = sa_family_t(AF_INET)
                addr.sin_port = UInt16(9).bigEndian
                guard inet_pton(AF_INET, ip, &addr.sin_addr) == 1 else { continue }
                withUnsafePointer(to: &addr) { ptr in
                    ptr.withMemoryRebound(to: sockaddr.self, capacity: 1) { sockPtr in
                        _ = sendto(fd, &payload, 1, 0, sockPtr, socklen_t(MemoryLayout<sockaddr_in>.size))
                    }
                }
            }
            // Give the LAN ~350ms to reply to ARP requests.
            usleep(350_000)
        }.value
    }

    /// Briefly browses common mDNS/Bonjour service types to enrich device names & roles.
    private static func browseMDNSServices(durationSeconds: TimeInterval) async -> [String: [String]] {
        let serviceTypes = [
            "_http._tcp",
            "_https._tcp",
            "_airplay._tcp",
            "_raop._tcp",
            "_googlecast._tcp",
            "_hap._tcp",
            "_ipp._tcp",
            "_smb._tcp",
            "_ssh._tcp",
            "_adb._tcp",
        ]

        let lock = NSLock()
        var found: [String: Set<String>] = [:]
        let queue = DispatchQueue(label: "io.github.imjasonh.lantern.mdns", qos: .utility)
        var browsers: [NWBrowser] = []

        for type in serviceTypes {
            let browser = NWBrowser(for: .bonjour(type: type, domain: "local."), using: .tcp)
            browser.browseResultsChangedHandler = { results, _ in
                lock.lock()
                for result in results {
                    if case .service(let name, let svcType, _, _) = result.endpoint {
                        let key = name.lowercased()
                        found[key, default: []].insert(svcType)
                    }
                }
                lock.unlock()
            }
            browser.start(queue: queue)
            browsers.append(browser)
        }

        let nanos = UInt64(max(0.2, durationSeconds) * 1_000_000_000)
        try? await Task.sleep(nanoseconds: nanos)

        for browser in browsers {
            browser.cancel()
        }

        lock.lock()
        let snapshot = found.mapValues { Array($0).sorted() }
        lock.unlock()
        return snapshot
    }
}
