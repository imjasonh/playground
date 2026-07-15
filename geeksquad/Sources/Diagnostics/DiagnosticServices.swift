import CoreWLAN
import Darwin
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
        let rate = iface.transmitRate
        let body = [
            "Interface: \(iface.interfaceName ?? "?")",
            "SSID: \(ssid)",
            "BSSID: \(bssid)",
            "Transmit rate: \(rate) Mbps",
            "Note: RSSI/channel surveys are intentionally out of scope for v1.",
            "Note: Location permission may be required to reveal SSID/BSSID."
        ].joined(separator: "\n")
        return DiagnosticReport(title: "Current Wi‑Fi", body: body, proposedFixes: [])
    }

    // MARK: - Process CPU / memory

    /// Live RSS/%CPU for processes matching `query` (app name fragment).
    func processUsage(query: String) async -> DiagnosticReport {
        let q = query.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !q.isEmpty else {
            return DiagnosticReport(
                title: "Process usage",
                body: "Enter an app or process name (e.g. Cursor, Safari, Chrome).",
                proposedFixes: []
            )
        }
        do {
            let result = try ProcessRunner.run(
                "/bin/ps",
                arguments: ["-axo", "pid=,rss=,%cpu=,command="],
                timeoutSeconds: 6,
                maxOutputBytes: 512_000
            )
            if result.timedOut {
                return DiagnosticReport(
                    title: "Process usage",
                    body: "Timed out listing processes.",
                    proposedFixes: ["Try again, or open Activity Monitor for a live view."]
                )
            }
            let rows = ProcessListParser.parse(result.stdout)
            let matches = ProcessListParser.matching(rows, query: q)
            let summary = ProcessListParser.summarize(
                matches: matches,
                query: q,
                physicalMemoryBytes: physicalMemoryBytes()
            )
            return DiagnosticReport(
                title: "Process usage",
                body: summary.body,
                proposedFixes: summary.proposedFixes
            )
        } catch {
            return DiagnosticReport(
                title: "Process usage",
                body: "Failed to list processes: \(error.localizedDescription)",
                proposedFixes: ["Open Activity Monitor as a fallback."]
            )
        }
    }

    /// Top processes by RSS — for “what’s using my memory?”
    func topMemoryProcesses(limit: Int = 15) async -> DiagnosticReport {
        let cap = min(max(limit, 5), 25)
        do {
            let result = try ProcessRunner.run(
                "/bin/ps",
                arguments: ["-axo", "pid=,rss=,%cpu=,command="],
                timeoutSeconds: 6,
                maxOutputBytes: 512_000
            )
            if result.timedOut {
                return DiagnosticReport(
                    title: "Top memory",
                    body: "Timed out listing processes.",
                    proposedFixes: ["Try again, or open Activity Monitor."]
                )
            }
            let rows = ProcessListParser.parse(result.stdout)
                .sorted { $0.rssKilobytes > $1.rssKilobytes }
            let top = Array(rows.prefix(cap))
            let ramGB = Double(physicalMemoryBytes()) / 1_073_741_824.0
            var lines: [String] = [
                String(format: "Physical RAM: %.1f GB", ramGB),
                "Top \(top.count) by memory (RSS):",
                "",
            ]
            for row in top {
                lines.append(
                    String(
                        format: "  pid %-6d  %7.0f MB  %5.1f%% CPU  %@",
                        row.pid,
                        row.rssMegabytes,
                        row.cpuPercent,
                        row.shortName
                    )
                )
            }
            return DiagnosticReport(
                title: "Top memory",
                body: lines.joined(separator: "\n"),
                proposedFixes: [
                    "If one app dominates, quit/relaunch it. Geek Squad does not kill processes for you.",
                    "For a named app, run Process usage with that name for a full helper breakdown.",
                ]
            )
        } catch {
            return DiagnosticReport(
                title: "Top memory",
                body: "Failed to list processes: \(error.localizedDescription)",
                proposedFixes: ["Open Activity Monitor as a fallback."]
            )
        }
    }

    /// Top processes by %CPU.
    func topCPUProcesses(limit: Int = 15) async -> DiagnosticReport {
        let cap = min(max(limit, 5), 25)
        do {
            let result = try ProcessRunner.run(
                "/bin/ps",
                arguments: ["-axo", "pid=,rss=,%cpu=,command="],
                timeoutSeconds: 6,
                maxOutputBytes: 512_000
            )
            if result.timedOut {
                return DiagnosticReport(
                    title: "Top CPU",
                    body: "Timed out listing processes.",
                    proposedFixes: ["Try again, or open Activity Monitor."]
                )
            }
            let rows = ProcessListParser.parse(result.stdout)
                .sorted { $0.cpuPercent > $1.cpuPercent }
            let top = Array(rows.prefix(cap))
            var lines: [String] = ["Top \(top.count) by CPU %:", ""]
            for row in top {
                lines.append(
                    String(
                        format: "  pid %-6d  %5.1f%% CPU  %7.0f MB  %@",
                        row.pid,
                        row.cpuPercent,
                        row.rssMegabytes,
                        row.shortName
                    )
                )
            }
            let hot = top.first.map(\.cpuPercent) ?? 0
            var fixes = [
                "If one process is pegging a core, quit/relaunch that app. Geek Squad does not kill processes for you."
            ]
            if hot >= 80 {
                fixes.insert(
                    String(format: "At least one process is very hot (%.0f%% CPU). Check whether it’s stuck or doing expected work.", hot),
                    at: 0
                )
            }
            if top.contains(where: ProcessListParser.isSpotlightRelated) {
                fixes.insert(
                    "Spotlight indexing (mds/mdworker) is among the hot processes. After large file copies or OS updates this is normal — wait it out, or check System Settings → Siri & Spotlight. Avoid force-quitting mdworker repeatedly.",
                    at: 0
                )
            }
            return DiagnosticReport(title: "Top CPU", body: lines.joined(separator: "\n"), proposedFixes: fixes)
        } catch {
            return DiagnosticReport(
                title: "Top CPU",
                body: "Failed to list processes: \(error.localizedDescription)",
                proposedFixes: ["Open Activity Monitor as a fallback."]
            )
        }
    }

    func diskSpace() async -> DiagnosticReport {
        do {
            let result = try ProcessRunner.run(
                "/bin/df",
                arguments: ["-kP"],
                timeoutSeconds: 5,
                maxOutputBytes: 64_000
            )
            if result.timedOut {
                return DiagnosticReport(
                    title: "Disk space",
                    body: "Timed out running df.",
                    proposedFixes: ["Open Disk Utility or Apple menu → About This Mac → Storage."]
                )
            }
            let volumes = DiskSpaceParser.parse(result.stdout)
            let summary = DiskSpaceParser.summarize(volumes)
            return DiagnosticReport(title: "Disk space", body: summary.body, proposedFixes: summary.proposedFixes)
        } catch {
            return DiagnosticReport(
                title: "Disk space",
                body: "Failed to run df: \(error.localizedDescription)",
                proposedFixes: ["Open System Settings → General → Storage."]
            )
        }
    }

    func memoryPressure() async -> DiagnosticReport {
        do {
            let result = try ProcessRunner.run(
                "/usr/bin/vm_stat",
                arguments: [],
                timeoutSeconds: 5,
                maxOutputBytes: 32_000
            )
            if result.timedOut {
                return DiagnosticReport(
                    title: "Memory pressure",
                    body: "Timed out running vm_stat.",
                    proposedFixes: ["Open Activity Monitor → Memory."]
                )
            }
            guard let stats = VmStatParser.parse(result.stdout) else {
                return DiagnosticReport(
                    title: "Memory pressure",
                    body: "Could not parse vm_stat output:\n\(result.stdout.prefix(500))",
                    proposedFixes: ["Open Activity Monitor → Memory."]
                )
            }
            let summary = VmStatParser.summarize(stats, physicalMemoryBytes: physicalMemoryBytes())
            return DiagnosticReport(
                title: "Memory pressure",
                body: summary.body,
                proposedFixes: summary.proposedFixes
            )
        } catch {
            return DiagnosticReport(
                title: "Memory pressure",
                body: "Failed to run vm_stat: \(error.localizedDescription)",
                proposedFixes: ["Open Activity Monitor → Memory."]
            )
        }
    }

    func systemLoad() async -> DiagnosticReport {
        var lines: [String] = []
        var fixes: [String] = []

        var load = [Double](repeating: 0, count: 3)
        var loadCount = 3
        if getloadavg(&load, Int32(loadCount)) != -1 {
            lines.append(
                String(format: "Load average (1/5/15 min): %.2f  %.2f  %.2f", load[0], load[1], load[2])
            )
            let cores = Double(ProcessInfo.processInfo.processorCount)
            lines.append("Logical CPUs: \(ProcessInfo.processInfo.processorCount)")
            if load[0] > cores * 1.5 {
                fixes.append(
                    String(
                        format: "1-minute load (%.2f) is high vs %d CPUs — check top_cpu for what’s busy.",
                        load[0],
                        ProcessInfo.processInfo.processorCount
                    )
                )
            }
        }

        do {
            let result = try ProcessRunner.run(
                "/usr/bin/uptime",
                arguments: [],
                timeoutSeconds: 3,
                maxOutputBytes: 4_000
            )
            let text = result.stdout.trimmingCharacters(in: .whitespacesAndNewlines)
            if !text.isEmpty { lines.append("uptime: \(text)") }
        } catch {
            lines.append("uptime unavailable: \(error.localizedDescription)")
        }

        let uptime = ProcessInfo.processInfo.systemUptime
        let days = Int(uptime) / 86_400
        let hours = (Int(uptime) % 86_400) / 3600
        lines.append("Host uptime: \(days)d \(hours)h")
        if days >= 14 {
            fixes.append("This Mac has been up \(days) days — a restart can clear leaked resources and stuck helpers.")
        }
        if fixes.isEmpty {
            fixes.append("Load looks manageable from this snapshot. If things still feel slow, check disk_space, memory_pressure, and top_cpu.")
        }
        return DiagnosticReport(title: "System load", body: lines.joined(separator: "\n"), proposedFixes: fixes)
    }

    func powerAssertions() async -> DiagnosticReport {
        do {
            let result = try ProcessRunner.run(
                "/usr/bin/pmset",
                arguments: ["-g", "assertions"],
                timeoutSeconds: 6,
                maxOutputBytes: 96_000
            )
            if result.timedOut {
                return DiagnosticReport(
                    title: "Power assertions",
                    body: "Timed out running pmset.",
                    proposedFixes: ["Try `pmset -g assertions` in Terminal."]
                )
            }
            let text = result.stdout.trimmingCharacters(in: .whitespacesAndNewlines)
            guard !text.isEmpty else {
                return DiagnosticReport(
                    title: "Power assertions",
                    body: "No pmset assertions output.",
                    proposedFixes: []
                )
            }
            let clipped = text.count > 4_000 ? String(text.prefix(4_000)) + "\n…(truncated)" : text
            var fixes: [String] = [
                "Assertions that prevent idle sleep often come from video, backups, or busy apps. Quit the named process if sleep/fans are the issue. Geek Squad does not clear assertions for you."
            ]
            if text.localizedCaseInsensitiveContains("PreventUserIdleSystemSleep")
                || text.localizedCaseInsensitiveContains("PreventSystemSleep")
            {
                fixes.insert(
                    "Something is asserting PreventUserIdleSystemSleep / PreventSystemSleep — see the process names in the report above.",
                    at: 0
                )
            }
            return DiagnosticReport(title: "Power assertions", body: clipped, proposedFixes: fixes)
        } catch {
            return DiagnosticReport(
                title: "Power assertions",
                body: "Failed to run pmset: \(error.localizedDescription)",
                proposedFixes: []
            )
        }
    }

    /// Listening TCP ports; optional `port` filters to one port (e.g. 3000).
    func listeningPorts(port: Int? = nil) async -> DiagnosticReport {
        do {
            let result = try ProcessRunner.run(
                "/usr/sbin/lsof",
                arguments: ["-nP", "-iTCP", "-sTCP:LISTEN"],
                timeoutSeconds: 8,
                maxOutputBytes: 256_000
            )
            if result.timedOut {
                return DiagnosticReport(
                    title: "Listening ports",
                    body: "Timed out running lsof.",
                    proposedFixes: ["Try again; lsof can be slow with many open files."]
                )
            }
            // lsof exits 1 when no matches — still parse stdout.
            let ports = ListeningPortsParser.parse(result.stdout + "\n" + result.stderr)
            let summary = ListeningPortsParser.summarize(ports, filterPort: port)
            return DiagnosticReport(
                title: "Listening ports",
                body: summary.body,
                proposedFixes: summary.proposedFixes
            )
        } catch {
            return DiagnosticReport(
                title: "Listening ports",
                body: "Failed to run lsof: \(error.localizedDescription)",
                proposedFixes: ["Try Activity Monitor or `lsof -nP -iTCP -sTCP:LISTEN` in Terminal."]
            )
        }
    }

    func recentCrashReports(query: String? = nil) async -> DiagnosticReport {
        let home = FileManager.default.homeDirectoryForCurrentUser
        let dirs = [
            home.appendingPathComponent("Library/Logs/DiagnosticReports"),
            URL(fileURLWithPath: "/Library/Logs/DiagnosticReports"),
        ]
        let files = CrashReportsScanner.scan(directories: dirs, query: query, limit: 15)
        let summary = CrashReportsScanner.summarize(files, query: query)
        return DiagnosticReport(
            title: "Crash reports",
            body: summary.body,
            proposedFixes: summary.proposedFixes
        )
    }

    /// Login/launch agents from standard LaunchAgents/LaunchDaemons directories.
    func loginItems() async -> DiagnosticReport {
        let home = FileManager.default.homeDirectoryForCurrentUser
        let dirs: [(URL, String)] = [
            (home.appendingPathComponent("Library/LaunchAgents"), "user"),
            (URL(fileURLWithPath: "/Library/LaunchAgents"), "local"),
            (URL(fileURLWithPath: "/Library/LaunchDaemons"), "system"),
        ]
        let items = LaunchAgentsParser.scan(directories: dirs.map { (url: $0.0, scope: $0.1) })
        let summary = LaunchAgentsParser.summarize(items)
        return DiagnosticReport(
            title: "Login / launch agents",
            body: summary.body,
            proposedFixes: summary.proposedFixes
        )
    }

    /// Approximate sizes of common user folders that eat disk.
    func userStorageHotspots() async -> DiagnosticReport {
        let home = FileManager.default.homeDirectoryForCurrentUser
        let targets: [(name: String, url: URL)] = [
            ("Downloads", home.appendingPathComponent("Downloads")),
            ("Desktop", home.appendingPathComponent("Desktop")),
            ("Documents", home.appendingPathComponent("Documents")),
            ("Library/Caches", home.appendingPathComponent("Library/Caches")),
            ("Library/Logs", home.appendingPathComponent("Library/Logs")),
            ("Movies", home.appendingPathComponent("Movies")),
        ]
        var samples: [FolderSizeSample] = []
        for target in targets {
            guard FileManager.default.fileExists(atPath: target.url.path) else {
                samples.append(
                    FolderSizeSample(name: target.name, path: target.url.path, kilobytes: nil, error: "missing")
                )
                continue
            }
            do {
                let result = try ProcessRunner.run(
                    "/usr/bin/du",
                    arguments: ["-sk", target.url.path],
                    timeoutSeconds: 12,
                    maxOutputBytes: 4_096
                )
                if result.timedOut {
                    samples.append(
                        FolderSizeSample(
                            name: target.name,
                            path: target.url.path,
                            kilobytes: nil,
                            error: "timed out (folder very large or slow disk)"
                        )
                    )
                } else if let kb = FolderSizeParser.parseDuSK(result.stdout) {
                    samples.append(
                        FolderSizeSample(name: target.name, path: target.url.path, kilobytes: kb, error: nil)
                    )
                } else {
                    samples.append(
                        FolderSizeSample(
                            name: target.name,
                            path: target.url.path,
                            kilobytes: nil,
                            error: "unparsed du output"
                        )
                    )
                }
            } catch {
                samples.append(
                    FolderSizeSample(
                        name: target.name,
                        path: target.url.path,
                        kilobytes: nil,
                        error: error.localizedDescription
                    )
                )
            }
        }
        let summary = FolderSizeParser.summarize(samples)
        return DiagnosticReport(
            title: "User storage hotspots",
            body: summary.body,
            proposedFixes: summary.proposedFixes
        )
    }

    /// Battery / AC power snapshot (`pmset -g batt`).
    func batteryPower() async -> DiagnosticReport {
        do {
            let result = try ProcessRunner.run(
                "/usr/bin/pmset",
                arguments: ["-g", "batt"],
                timeoutSeconds: 5,
                maxOutputBytes: 8_000
            )
            if result.timedOut {
                return DiagnosticReport(
                    title: "Battery / power",
                    body: "Timed out running pmset.",
                    proposedFixes: ["Open System Settings → Battery."]
                )
            }
            let text = result.stdout.trimmingCharacters(in: .whitespacesAndNewlines)
            guard !text.isEmpty else {
                return DiagnosticReport(
                    title: "Battery / power",
                    body: "No battery info (desktop Mac without UPS, or pmset returned empty).",
                    proposedFixes: []
                )
            }
            var fixes: [String] = []
            let lower = text.lowercased()
            if lower.contains("battery power") {
                fixes.append("You’re on battery. For heavy work (builds, video), plug in — Low Power Mode and thermal limits can make the Mac feel slower on battery.")
            }
            if lower.contains("charging") {
                fixes.append("Battery is charging. Performance should be closer to AC adapter levels once charged, depending on thermal state.")
            }
            if let pct = BatteryPowerParser.percent(from: text), pct <= 20 {
                fixes.append("Battery is at \(pct)%. Plug in if the Mac feels throttled or you need sustained CPU.")
            }
            if fixes.isEmpty {
                fixes.append("Power source looks fine from pmset. If fans are loud on AC, check power_assertions and top_cpu next.")
            }
            return DiagnosticReport(title: "Battery / power", body: text, proposedFixes: fixes)
        } catch {
            return DiagnosticReport(
                title: "Battery / power",
                body: "Failed to run pmset: \(error.localizedDescription)",
                proposedFixes: ["Open System Settings → Battery."]
            )
        }
    }

    private func physicalMemoryBytes() -> UInt64 {
        var size: UInt64 = 0
        var len = MemoryLayout<UInt64>.size
        let result = sysctlbyname("hw.memsize", &size, &len, nil, 0)
        return result == 0 ? size : 0
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
