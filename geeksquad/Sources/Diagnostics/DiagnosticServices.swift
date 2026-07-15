import CoreWLAN
import Foundation
import Network

/// Live diagnostic checks for the Manual Toolbox. Prefer Network /
/// SystemConfiguration / CoreWLAN; fall back to CLI helpers with timeouts.
struct DiagnosticServices: Sendable {
    static let shared = DiagnosticServices()

    // MARK: - Interfaces

    func interfaces() async -> DiagnosticReport {
        var lines: [String] = []
        var utun: [String] = []

        for name in sortedInterfaceNames() {
            var ipv4: [String] = []
            var ipv6: [String] = []
            if let addrs = getInterfaceAddresses(name) {
                ipv4 = addrs.v4
                ipv6 = addrs.v6
            }
            let flag = name.hasPrefix("utun") || name.hasPrefix("ipsec") ? " (VPN-like)" : ""
            if flag.isEmpty == false { utun.append(name) }
            var line = "\(name)\(flag)"
            if !ipv4.isEmpty { line += "  IPv4 \(ipv4.joined(separator: ", "))" }
            if !ipv6.isEmpty { line += "  IPv6 \(ipv6.prefix(2).joined(separator: ", "))" }
            if ipv4.isEmpty && ipv6.isEmpty { line += "  (no unicast addr)" }
            lines.append(line)
        }

        var fixes: [String] = []
        if !utun.isEmpty {
            fixes.append(
                "VPN-like interfaces present (\(utun.joined(separator: ", "))). If browsing fails only with VPN up, disconnect VPN and retest."
            )
        }

        let body = lines.isEmpty ? "No interfaces found." : lines.joined(separator: "\n")
        return DiagnosticReport(title: "Interfaces", body: body, proposedFixes: fixes)
    }

    // MARK: - Default route

    func defaultRoute() async -> DiagnosticReport {
        // Prefer `route get default` — SCDynamicStore route keys vary by OS.
        do {
            let result = try ProcessRunner.run("/sbin/route", arguments: ["-n", "get", "default"])
            if result.timedOut {
                return DiagnosticReport(
                    title: "Default route",
                    body: "Timed out running route get default.",
                    proposedFixes: ProposedFixes.forDefaultRoute(interface: nil, gateway: nil, isVpn: false)
                )
            }
            let text = result.stdout.isEmpty ? result.stderr : result.stdout
            let iface = matchValue(in: text, key: "interface")
            let gateway = matchValue(in: text, key: "gateway")
            let isVpn = (iface ?? "").hasPrefix("utun")
                || (iface ?? "").hasPrefix("ipsec")
                || text.localizedCaseInsensitiveContains("utun")
            let fixes = ProposedFixes.forDefaultRoute(interface: iface, gateway: gateway, isVpn: isVpn)
            let body = text.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty
                ? "No default route output (exit \(result.exitCode))."
                : text.trimmingCharacters(in: .whitespacesAndNewlines)
            return DiagnosticReport(title: "Default route", body: body, proposedFixes: fixes)
        } catch {
            return DiagnosticReport(
                title: "Default route",
                body: "Failed to run route: \(error.localizedDescription)",
                proposedFixes: ProposedFixes.forDefaultRoute(interface: nil, gateway: nil, isVpn: false)
            )
        }
    }

    // MARK: - Path status

    func pathStatus() async -> DiagnosticReport {
        let path = await currentPath()
        var lines: [String] = []
        lines.append("Status: \(path.statusLabel)")
        lines.append("Expensive: \(path.isExpensive ? "yes" : "no")")
        lines.append("Constrained: \(path.isConstrained ? "yes" : "no")")
        if !path.interfaces.isEmpty {
            lines.append("Interfaces: \(path.interfaces.joined(separator: ", "))")
        }
        lines.append("Supports IPv4: \(path.supportsIPv4 ? "yes" : "no")")
        lines.append("Supports IPv6: \(path.supportsIPv6 ? "yes" : "no")")
        lines.append("Supports DNS: \(path.supportsDNS ? "yes" : "no")")

        let fixes = path.isSatisfied ? [] : ProposedFixes.forPathUnsatisfied()
        return DiagnosticReport(
            title: "Path status",
            body: lines.joined(separator: "\n"),
            proposedFixes: fixes
        )
    }

    // MARK: - DNS config

    func dnsConfig() async -> DiagnosticReport {
        do {
            let result = try ProcessRunner.run("/usr/sbin/scutil", arguments: ["--dns"])
            if result.timedOut {
                return DiagnosticReport(
                    title: "DNS config",
                    body: "Timed out running scutil --dns.",
                    proposedFixes: ProposedFixes.forDnsConfig(resolvers: [])
                )
            }
            let summary = DnsConfigParser.parse(result.stdout)
            let fixes = ProposedFixes.forDnsConfig(resolvers: summary.resolvers)
            return DiagnosticReport(
                title: "DNS config",
                body: summary.description,
                proposedFixes: fixes
            )
        } catch {
            return DiagnosticReport(
                title: "DNS config",
                body: "Failed: \(error.localizedDescription)",
                proposedFixes: ProposedFixes.forDnsConfig(resolvers: [])
            )
        }
    }

    // MARK: - DNS lookup

    func dnsLookup(hostname: String) async -> DiagnosticReport {
        let host = hostname.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !host.isEmpty else {
            return DiagnosticReport(title: "DNS lookup", body: "Enter a hostname.", proposedFixes: [])
        }

        // Prefer dig for readable A/AAAA records (timeout-bounded).
        var sections: [String] = []
        do {
            let a = try ProcessRunner.run(
                "/usr/bin/dig",
                arguments: ["+time=3", "+tries=1", "+short", "A", host]
            )
            let aaaa = try ProcessRunner.run(
                "/usr/bin/dig",
                arguments: ["+time=3", "+tries=1", "+short", "AAAA", host]
            )
            let aOut = a.stdout.trimmingCharacters(in: .whitespacesAndNewlines)
            let aaaaOut = aaaa.stdout.trimmingCharacters(in: .whitespacesAndNewlines)
            sections.append("A:\n\(aOut.isEmpty ? "(none)" : aOut)")
            sections.append("AAAA:\n\(aaaaOut.isEmpty ? "(none)" : aaaaOut)")
            if a.timedOut || aaaa.timedOut {
                sections.append("(one or more lookups timed out)")
            }
            var fixes: [String] = []
            if aOut.isEmpty && aaaaOut.isEmpty {
                fixes.append("No addresses returned — check DNS config and that the name is correct.")
                fixes.append("Try resolving an IP directly (reachability toolbox) to separate DNS from routing failures.")
            }
            return DiagnosticReport(
                title: "DNS lookup — \(host)",
                body: sections.joined(separator: "\n\n"),
                proposedFixes: fixes
            )
        } catch {
            return DiagnosticReport(
                title: "DNS lookup — \(host)",
                body: "dig failed: \(error.localizedDescription)",
                proposedFixes: ["Install or repair Command Line Tools if dig is missing, or check DNS config."]
            )
        }
    }

    // MARK: - Reachability (TCP)

    func reachability(host: String, port: UInt16) async -> DiagnosticReport {
        let trimmed = host.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            return DiagnosticReport(title: "Reachability", body: "Enter a host.", proposedFixes: [])
        }
        let ok = await tcpConnect(host: trimmed, port: port, timeout: 5)
        if ok {
            return DiagnosticReport(
                title: "Reachability — \(trimmed):\(port)",
                body: "TCP connect succeeded.",
                proposedFixes: []
            )
        }
        return DiagnosticReport(
            title: "Reachability — \(trimmed):\(port)",
            body: "TCP connect failed or timed out.",
            proposedFixes: [
                "If DNS lookup works but this fails, check firewall/VPN or that the port is open.",
                "Retry with port 443 against a known host (e.g. 1.1.1.1)."
            ]
        )
    }

    // MARK: - HTTP probe

    func httpProbe(urlString: String) async -> DiagnosticReport {
        let raw = urlString.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let url = URL(string: raw), url.scheme == "http" || url.scheme == "https" else {
            return DiagnosticReport(
                title: "HTTP probe",
                body: "Enter an http(s) URL.",
                proposedFixes: []
            )
        }

        var request = URLRequest(url: url, timeoutInterval: 10)
        request.httpMethod = "GET"
        request.setValue("GeekSquad/0.1", forHTTPHeaderField: "User-Agent")

        let start = Date()
        do {
            let (data, response) = try await URLSession.shared.data(for: request)
            let ms = Int(Date().timeIntervalSince(start) * 1000)
            let http = response as? HTTPURLResponse
            let status = http?.statusCode ?? -1
            let finalURL = http?.url?.absoluteString ?? url.absoluteString
            let bytes = data.count
            var lines = [
                "Status: \(status)",
                "Final URL: \(finalURL)",
                "Bytes: \(bytes)",
                "Time: \(ms) ms"
            ]
            if let mime = http?.mimeType {
                lines.append("MIME: \(mime)")
            }
            var fixes: [String] = []
            if status >= 400 || status < 0 {
                fixes = ProposedFixes.forHttpFailure(statusHint: "\(status)")
            }
            if finalURL != url.absoluteString {
                lines.append("Redirected from \(url.absoluteString)")
            }
            return DiagnosticReport(
                title: "HTTP probe",
                body: lines.joined(separator: "\n"),
                proposedFixes: fixes
            )
        } catch {
            let hint = error.localizedDescription
            return DiagnosticReport(
                title: "HTTP probe",
                body: "Request failed: \(hint)",
                proposedFixes: ProposedFixes.forHttpFailure(statusHint: hint)
            )
        }
    }

    // MARK: - Proxy config

    func proxyConfig() async -> DiagnosticReport {
        // networksetup needs a service name; enumerate via networksetup -listallnetworkservices
        do {
            let list = try ProcessRunner.run(
                "/usr/sbin/networksetup",
                arguments: ["-listallnetworkservices"]
            )
            let services = list.stdout
                .split(whereSeparator: \.isNewline)
                .map { $0.trimmingCharacters(in: .whitespaces) }
                .filter { !$0.isEmpty && !$0.hasPrefix("An asterisk") && !$0.hasPrefix("*") }
                // Lines may start with * for disabled
                .map { line -> String in
                    if line.hasPrefix("*") {
                        return String(line.dropFirst()).trimmingCharacters(in: .whitespaces)
                    }
                    return line
                }

            var lines: [String] = []
            var enabledServices: [String] = []
            for service in services.prefix(12) {
                let web = try ProcessRunner.run(
                    "/usr/sbin/networksetup",
                    arguments: ["-getwebproxy", service]
                )
                let secure = try ProcessRunner.run(
                    "/usr/sbin/networksetup",
                    arguments: ["-getsecurewebproxy", service]
                )
                let socks = try ProcessRunner.run(
                    "/usr/sbin/networksetup",
                    arguments: ["-getsocksfirewallproxy", service]
                )
                let webOn = web.stdout.localizedCaseInsensitiveContains("Enabled: Yes")
                let secureOn = secure.stdout.localizedCaseInsensitiveContains("Enabled: Yes")
                let socksOn = socks.stdout.localizedCaseInsensitiveContains("Enabled: Yes")
                if webOn || secureOn || socksOn {
                    enabledServices.append(service)
                }
                lines.append("\(service):")
                lines.append("  HTTP  \(webOn ? "on" : "off")")
                lines.append("  HTTPS \(secureOn ? "on" : "off")")
                lines.append("  SOCKS \(socksOn ? "on" : "off")")
            }

            let body = lines.isEmpty ? "No network services found." : lines.joined(separator: "\n")
            return DiagnosticReport(
                title: "Proxy config",
                body: body,
                proposedFixes: ProposedFixes.forProxyEnabled(services: enabledServices)
            )
        } catch {
            return DiagnosticReport(
                title: "Proxy config",
                body: "Failed: \(error.localizedDescription)",
                proposedFixes: []
            )
        }
    }

    // MARK: - VPN-like interfaces

    func vpnInterfaces() async -> DiagnosticReport {
        let names = sortedInterfaceNames().filter {
            $0.hasPrefix("utun") || $0.hasPrefix("ipsec") || $0.hasPrefix("ppp")
        }
        let path = await currentPath()
        var lines: [String] = []
        if names.isEmpty {
            lines.append("No utun/ipsec/ppp interfaces found.")
        } else {
            lines.append("VPN-like interfaces: \(names.joined(separator: ", "))")
        }
        lines.append("Current path interfaces: \(path.interfaces.joined(separator: ", "))")
        let usingVpn = path.interfaces.contains { $0.hasPrefix("utun") || $0.hasPrefix("ipsec") }
        lines.append("Path appears to use VPN iface: \(usingVpn ? "yes" : "no")")

        var fixes: [String] = []
        if usingVpn {
            fixes.append(
                "Traffic may be forced through VPN. If connectivity is broken, disconnect VPN and retest; check the VPN app’s DNS / split-tunnel options."
            )
        }
        return DiagnosticReport(title: "VPN interfaces", body: lines.joined(separator: "\n"), proposedFixes: fixes)
    }

    // MARK: - Hosts file

    func hostsFile() async -> DiagnosticReport {
        let path = "/etc/hosts"
        guard let data = FileManager.default.contents(atPath: path),
              let text = String(data: data, encoding: .utf8)
        else {
            return DiagnosticReport(
                title: "Hosts file",
                body: "Could not read \(path).",
                proposedFixes: []
            )
        }
        let summary = HostsFileParser.parse(text)
        return DiagnosticReport(
            title: "Hosts file",
            body: summary.description,
            proposedFixes: ProposedFixes.forHostsOverrides(count: summary.surprising.count)
        )
    }

    // MARK: - Current Wi‑Fi (optional)

    func currentWifi() async -> DiagnosticReport {
        let client = CWWiFiClient.shared()
        guard let iface = client.interface() else {
            return DiagnosticReport(
                title: "Current Wi‑Fi",
                body: "No Wi‑Fi interface available.",
                proposedFixes: []
            )
        }
        let ssid = iface.ssid() ?? "(SSID unavailable — grant Location, or not associated)"
        let bssid = iface.bssid() ?? "(BSSID unavailable)"
        let rate = iface.transmitRate()
        let body = [
            "Interface: \(iface.interfaceName() ?? "?")",
            "SSID: \(ssid)",
            "BSSID: \(bssid)",
            "Transmit rate: \(rate) Mbps",
            "Note: RSSI/channel surveys are intentionally out of scope for v1.",
            "Note: Location permission may be required to reveal SSID/BSSID."
        ].joined(separator: "\n")
        return DiagnosticReport(title: "Current Wi‑Fi", body: body, proposedFixes: [])
    }

    // MARK: - Helpers

    private struct PathSnapshot: Sendable {
        var statusLabel: String
        var isSatisfied: Bool
        var isExpensive: Bool
        var isConstrained: Bool
        var supportsIPv4: Bool
        var supportsIPv6: Bool
        var supportsDNS: Bool
        var interfaces: [String]
    }

    private func currentPath() async -> PathSnapshot {
        await withCheckedContinuation { continuation in
            let monitor = NWPathMonitor()
            let queue = DispatchQueue(label: "io.github.imjasonh.geeksquad.path")
            monitor.pathUpdateHandler = { path in
                monitor.cancel()
                var ifaces: [String] = []
                if #available(macOS 13.0, *) {
                    // NWPath uses path.availableInterfaces
                    ifaces = path.availableInterfaces.map(\.name)
                }
                let label: String
                switch path.status {
                case .satisfied: label = "satisfied"
                case .unsatisfied: label = "unsatisfied"
                case .requiresConnection: label = "requiresConnection"
                @unknown default: label = "unknown"
                }
                continuation.resume(
                    returning: PathSnapshot(
                        statusLabel: label,
                        isSatisfied: path.status == .satisfied,
                        isExpensive: path.isExpensive,
                        isConstrained: path.isConstrained,
                        supportsIPv4: path.supportsIPv4,
                        supportsIPv6: path.supportsIPv6,
                        supportsDNS: path.supportsDNS,
                        interfaces: ifaces
                    )
                )
            }
            monitor.start(queue: queue)
        }
    }

    private func tcpConnect(host: String, port: UInt16, timeout: TimeInterval) async -> Bool {
        await withCheckedContinuation { continuation in
            let connection = NWConnection(
                host: NWEndpoint.Host(host),
                port: NWEndpoint.Port(rawValue: port)!,
                using: .tcp
            )
            let lock = NSLock()
            var resumed = false
            let finish: (Bool) -> Void = { value in
                lock.lock()
                defer { lock.unlock() }
                guard !resumed else { return }
                resumed = true
                connection.cancel()
                continuation.resume(returning: value)
            }
            connection.stateUpdateHandler = { state in
                switch state {
                case .ready:
                    finish(true)
                case .failed, .cancelled:
                    finish(false)
                default:
                    break
                }
            }
            connection.start(queue: DispatchQueue(label: "io.github.imjasonh.geeksquad.tcp"))
            DispatchQueue.global().asyncAfter(deadline: .now() + timeout) {
                finish(false)
            }
        }
    }

    private func sortedInterfaceNames() -> [String] {
        var names: [String] = []
        var ifaddr: UnsafeMutablePointer<ifaddrs>?
        guard getifaddrs(&ifaddr) == 0, let first = ifaddr else { return [] }
        defer { freeifaddrs(ifaddr) }
        var ptr: UnsafeMutablePointer<ifaddrs>? = first
        var seen = Set<String>()
        while let p = ptr {
            let name = String(cString: p.pointee.ifa_name)
            if seen.insert(name).inserted {
                names.append(name)
            }
            ptr = p.pointee.ifa_next
        }
        return names.sorted()
    }

    private func getInterfaceAddresses(_ name: String) -> (v4: [String], v6: [String])? {
        var v4: [String] = []
        var v6: [String] = []
        var ifaddr: UnsafeMutablePointer<ifaddrs>?
        guard getifaddrs(&ifaddr) == 0, let first = ifaddr else { return nil }
        defer { freeifaddrs(ifaddr) }
        var ptr: UnsafeMutablePointer<ifaddrs>? = first
        while let p = ptr {
            let ifName = String(cString: p.pointee.ifa_name)
            if ifName == name, let addr = p.pointee.ifa_addr {
                let family = Int32(addr.pointee.sa_family)
                var host = [CChar](repeating: 0, count: Int(NI_MAXHOST))
                let len = socklen_t(addr.pointee.sa_len)
                if getnameinfo(addr, len, &host, socklen_t(host.count), nil, 0, NI_NUMERICHOST) == 0 {
                    let ip = String(cString: host)
                    if family == AF_INET { v4.append(ip) }
                    if family == AF_INET6 { v6.append(ip) }
                }
            }
            ptr = p.pointee.ifa_next
        }
        return (v4, v6)
    }

    private func matchValue(in text: String, key: String) -> String? {
        for raw in text.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            guard line.hasPrefix(key) else { continue }
            if let idx = line.firstIndex(of: ":") {
                let value = line[line.index(after: idx)...].trimmingCharacters(in: .whitespaces)
                if !value.isEmpty { return value }
            }
        }
        return nil
    }
}
