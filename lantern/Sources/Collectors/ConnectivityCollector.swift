import Foundation
import Network
import SystemConfiguration

/// Distilled connectivity health check (path, DNS, proxy, VPN, `/etc/hosts`, captive portal).
enum ConnectivityCollector {
    static func collect(
        pathSatisfied: Bool,
        network: NetworkIdentity,
        runActiveProbes: Bool = false,
        now: Date = Date()
    ) async -> ConnectivityHealth {
        let dnsOut = (try? ProcessRunner.run("/usr/sbin/scutil", arguments: ["--dns"], timeoutSeconds: 4))?.stdout ?? ""
        let dnsServers = parseDNSServers(dnsOut)

        let proxy = readSystemProxyConfig()
        let vpnIfaces = activeVPNInterfaces()
        let hostsText = (try? String(contentsOfFile: "/etc/hosts", encoding: .utf8)) ?? ""
        let suspiciousHosts = parseSuspiciousHostsEntries(hostsText)

        var dnsResolves: Bool?
        var httpProbeOK: Bool?
        var captivePortal = false

        if runActiveProbes && pathSatisfied {
            let digRes = try? ProcessRunner.run(
                "/usr/bin/dig",
                arguments: ["+short", "+time=2", "+tries=1", "example.com", "A"],
                timeoutSeconds: 4
            )
            dnsResolves = (digRes?.exitCode == 0) && !(digRes?.stdout.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty ?? true)

            let probe = await probeCaptivePortal()
            httpProbeOK = probe.reachable
            captivePortal = probe.captivePortalSuspected
        }

        return ConnectivityHealth(
            isPathSatisfied: pathSatisfied,
            defaultInterface: network.interfaceName,
            defaultGateway: network.gatewayIP,
            isVPNActive: !vpnIfaces.isEmpty || (network.interfaceName?.hasPrefix("utun") ?? false),
            vpnInterfaces: vpnIfaces,
            dnsServers: dnsServers,
            proxyEnabled: proxy.enabled,
            proxySummary: proxy.summary,
            suspiciousHostsEntries: suspiciousHosts,
            dnsResolves: dnsResolves,
            httpProbeOK: httpProbeOK,
            captivePortalSuspected: captivePortal,
            checkedAt: now
        )
    }

    // MARK: - Pure parsers (unit-tested)

    static func parseDNSServers(_ scutilOutput: String) -> [String] {
        var servers: [String] = []
        var seen: Set<String> = []
        for rawLine in scutilOutput.split(separator: "\n") {
            let line = rawLine.trimmingCharacters(in: .whitespaces)
            guard line.hasPrefix("nameserver[") else { continue }
            if let colon = line.firstIndex(of: ":") {
                let ip = String(line[line.index(after: colon)...]).trimmingCharacters(in: .whitespaces)
                if !ip.isEmpty, seen.insert(ip).inserted {
                    servers.append(ip)
                }
            }
        }
        return servers
    }

    /// Flags non-standard `/etc/hosts` entries (anything beyond localhost / broadcasthost).
    static func parseSuspiciousHostsEntries(_ hostsContent: String) -> [String] {
        let standardHosts: Set<String> = ["localhost", "broadcasthost", "ip6-localhost", "ip6-loopback"]
        var results: [String] = []
        for rawLine in hostsContent.split(separator: "\n") {
            let stripped = rawLine.split(separator: "#", maxSplits: 1).first.map(String.init) ?? ""
            let trimmed = stripped.trimmingCharacters(in: .whitespaces)
            guard !trimmed.isEmpty else { continue }
            let tokens = trimmed.split(whereSeparator: { $0 == " " || $0 == "\t" }).map(String.init)
            guard tokens.count >= 2 else { continue }
            let hostnames = tokens.dropFirst()
            if hostnames.contains(where: { !standardHosts.contains($0.lowercased()) }) {
                results.append(trimmed)
            }
        }
        return results
    }

    // MARK: - macOS framework reads

    private static func readSystemProxyConfig() -> (enabled: Bool, summary: String?) {
        guard let dict = SCDynamicStoreCopyProxies(nil) as? [String: Any] else {
            return (false, nil)
        }
        var parts: [String] = []
        if (dict[kSCPropNetProxiesHTTPEnable as String] as? Int) == 1,
           let host = dict[kSCPropNetProxiesHTTPProxy as String] as? String
        {
            let port = dict[kSCPropNetProxiesHTTPPort as String] as? Int ?? 80
            parts.append("HTTP \(host):\(port)")
        }
        if (dict[kSCPropNetProxiesHTTPSEnable as String] as? Int) == 1,
           let host = dict[kSCPropNetProxiesHTTPSProxy as String] as? String
        {
            let port = dict[kSCPropNetProxiesHTTPSPort as String] as? Int ?? 443
            parts.append("HTTPS \(host):\(port)")
        }
        if (dict[kSCPropNetProxiesSOCKSEnable as String] as? Int) == 1,
           let host = dict[kSCPropNetProxiesSOCKSProxy as String] as? String
        {
            let port = dict[kSCPropNetProxiesSOCKSPort as String] as? Int ?? 1080
            parts.append("SOCKS \(host):\(port)")
        }
        if (dict[kSCPropNetProxiesProxyAutoConfigEnable as String] as? Int) == 1,
           let pac = dict[kSCPropNetProxiesProxyAutoConfigURLString as String] as? String
        {
            parts.append("PAC \(pac)")
        }
        return (!parts.isEmpty, parts.isEmpty ? nil : parts.joined(separator: ", "))
    }

    private static func activeVPNInterfaces() -> [String] {
        var ifaddr: UnsafeMutablePointer<ifaddrs>?
        guard getifaddrs(&ifaddr) == 0, let first = ifaddr else { return [] }
        defer { freeifaddrs(ifaddr) }

        var names: Set<String> = []
        var ptr: UnsafeMutablePointer<ifaddrs>? = first
        while let current = ptr {
            let flags = Int32(current.pointee.ifa_flags)
            let isUp = (flags & IFF_UP) != 0 && (flags & IFF_RUNNING) != 0
            let name = String(cString: current.pointee.ifa_name)
            if isUp,
               (name.hasPrefix("utun") || name.hasPrefix("ipsec") || name.hasPrefix("ppp")),
               let addr = current.pointee.ifa_addr,
               (addr.pointee.sa_family == UInt8(AF_INET) || addr.pointee.sa_family == UInt8(AF_INET6))
            {
                names.insert(name)
            }
            ptr = current.pointee.ifa_next
        }
        return names.sorted()
    }

    private static func probeCaptivePortal() async -> (reachable: Bool, captivePortalSuspected: Bool) {
        guard let url = URL(string: "http://captive.apple.com/hotspot-detect.html") else {
            return (false, false)
        }
        var req = URLRequest(url: url, timeoutInterval: 4)
        req.cachePolicy = .reloadIgnoringLocalAndRemoteCacheData
        guard let (data, resp) = try? await URLSession.shared.data(for: req),
              let http = resp as? HTTPURLResponse
        else {
            return (false, false)
        }
        let body = String(data: data, encoding: .utf8) ?? ""
        if http.statusCode == 200 && body.contains("Success") {
            return (true, false)
        }
        // Redirect or unexpected HTML on Apple's captive endpoint = captive portal.
        return (true, true)
    }
}
