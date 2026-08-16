import Foundation

/// Runs offline connectivity playbooks: gather checks → structured snapshot → ranked triage card.
enum ConnectivityPlaybookRunner {
    static func run(
        kind: ConnectivityPlaybookKind,
        services: DiagnosticServices = .shared,
        onProgress: (@Sendable (String) async -> Void)? = nil
    ) async -> PlaybookResult {
        let snapshot = await gather(
            kind: kind,
            services: services,
            onProgress: onProgress
        )
        let outcome = ConnectivityAnalyzer.analyze(snapshot, kind: kind)
        return PlaybookResult(
            kind: kind,
            triage: outcome.report,
            checks: snapshot.checkReports,
            actions: outcome.actions,
            looksOnline: outcome.looksOnline
        )
    }

    // MARK: - Gather

    static func gather(
        kind: ConnectivityPlaybookKind,
        services: DiagnosticServices = .shared,
        onProgress: (@Sendable (String) async -> Void)? = nil
    ) async -> ConnectivitySnapshot {
        if let onProgress {
            await onProgress("Checking network path…")
        }
        async let pathReport = services.pathStatus()
        async let routeReport = services.defaultRoute()
        async let dnsReport = services.dnsConfig()
        async let proxyReport = services.proxyConfig()
        async let vpnReport = services.vpnInterfaces()
        async let hostsReport = services.hostsFile()
        async let wifiReport = services.currentWifi()

        let path = await pathReport
        let route = await routeReport
        let dns = await dnsReport
        let proxy = await proxyReport
        let vpn = await vpnReport
        let hosts = await hostsReport
        let wifi = await wifiReport

        var snap = ConnectivitySnapshot()
        applyPath(path.body, into: &snap)
        applyRoute(route.body, into: &snap)
        applyDnsConfig(from: dns.body, into: &snap)
        applyProxy(proxy.body, into: &snap)
        applyVpn(vpn.body, into: &snap)
        applyHosts(hosts.body, into: &snap)
        applyWifi(wifi.body, into: &snap)

        // Enrich DNS resolvers from live scutil when body parse is thin.
        if snap.dnsResolvers.isEmpty {
            if let raw = try? ProcessRunner.run("/usr/sbin/scutil", arguments: ["--dns"]),
               !raw.timedOut
            {
                let summary = DnsConfigParser.parse(raw.stdout)
                snap.dnsResolvers = summary.resolvers
                snap.dnsSearchDomains = summary.searchDomains
            }
        }

        if let onProgress {
            await onProgress("Probing DNS and connectivity…")
        }
        async let lookupReport = services.dnsLookup(hostname: "example.com")
        async let reachReport = services.reachability(host: "1.1.1.1", port: 443)
        async let httpReport = services.httpProbe(urlString: "https://example.com")
        async let captiveReport = services.httpProbe(
            urlString: "http://captive.apple.com/hotspot-detect.html"
        )

        let lookup = await lookupReport
        let reach = await reachReport
        let http = await httpReport
        let captive = await captiveReport

        snap.dnsLookupOk = dnsLookupSucceeded(lookup.body)
        snap.dnsLookupDetail = lookup.body

        snap.tcpCloudflareOk = reach.body.localizedCaseInsensitiveContains("succeeded")
        snap.httpExampleStatus = statusCode(from: http.body)
        snap.httpExampleOk = (snap.httpExampleStatus.map { (200..<400).contains($0) } ?? false)
            && !http.body.localizedCaseInsensitiveContains("Request failed")
        snap.httpExampleDetail = http.body

        applyCaptive(captive, into: &snap)

        var checks: [DiagnosticReport] = [
            path, route, dns, proxy, vpn, hosts, wifi, lookup, reach, http, captive,
        ]

        // Extra probes for specific playbooks / fuller cant-get-online.
        if kind == .cantGetOnline || kind == .vpnBroken || kind == .someSitesFail {
            if let onProgress {
                await onProgress("Ping and second reachability probe…")
            }
            async let pingReport = services.ping(host: "1.1.1.1")
            async let reach2 = services.reachability(host: "8.8.8.8", port: 443)
            let ping = await pingReport
            let r2 = await reach2
            snap.tcpGoogleDnsOk = r2.body.localizedCaseInsensitiveContains("succeeded")
            if let loss = PingOutputParser.summarize(ping.body).lossPercent {
                snap.pingLossPercent = loss
            }
            snap.pingDetail = ping.body
            checks.append(contentsOf: [ping, r2])
        }

        if kind == .dnsWrong {
            if let onProgress {
                await onProgress("DNS delegation trace…")
            }
            let trace = await services.dnsTrace(hostname: "example.com")
            checks.append(trace)
        }

        snap.checkReports = checks
        if let onProgress {
            await onProgress("Ranking likely causes…")
        }
        return snap
    }

    // MARK: - Body parsers (toolbox report text → snapshot fields)

    static func applyPath(_ body: String, into snap: inout ConnectivitySnapshot) {
        for raw in body.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            if line.hasPrefix("Status:") {
                let value = valueAfterColon(line)?.lowercased()
                snap.pathStatusLabel = value
                snap.pathSatisfied = value == "satisfied"
            } else if line.hasPrefix("Expensive:") {
                snap.pathExpensive = valueAfterColon(line)?.lowercased() == "yes"
            } else if line.hasPrefix("Interfaces:") {
                let value = valueAfterColon(line) ?? ""
                snap.pathInterfaces = value
                    .split(separator: ",")
                    .map { $0.trimmingCharacters(in: .whitespaces) }
                    .filter { !$0.isEmpty }
            }
        }
    }

    static func applyRoute(_ body: String, into snap: inout ConnectivitySnapshot) {
        if body.localizedCaseInsensitiveContains("Failed to run route")
            || body.localizedCaseInsensitiveContains("No default route")
            || body.localizedCaseInsensitiveContains("not in table")
        {
            snap.hasDefaultRoute = false
        }
        snap.defaultInterface = matchRouteKey(body, key: "interface")
        snap.defaultGateway = matchRouteKey(body, key: "gateway")
        if snap.defaultInterface != nil || snap.defaultGateway != nil {
            snap.hasDefaultRoute = true
        }
        let iface = snap.defaultInterface ?? ""
        snap.defaultIsVpn = iface.hasPrefix("utun") || iface.hasPrefix("ipsec") || iface.hasPrefix("ppp")
            || body.localizedCaseInsensitiveContains("utun")
    }

    static func applyDnsConfig(from body: String, into snap: inout ConnectivitySnapshot) {
        var resolvers: [String] = []
        for raw in body.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            if line.hasPrefix("- ") {
                resolvers.append(String(line.dropFirst(2)))
            }
        }
        if body.localizedCaseInsensitiveContains("Resolvers: (none") {
            snap.dnsResolvers = []
        } else if !resolvers.isEmpty {
            snap.dnsResolvers = resolvers
        }
    }

    static func applyProxy(_ body: String, into snap: inout ConnectivitySnapshot) {
        var enabled: [String] = []
        var current: String?
        var serviceHasProxy = false
        for raw in body.split(whereSeparator: \.isNewline) {
            let line = String(raw)
            if !line.hasPrefix(" "), line.hasSuffix(":") {
                if let current, serviceHasProxy, !enabled.contains(current) {
                    enabled.append(current)
                }
                current = String(line.dropLast())
                serviceHasProxy = false
            } else if line.contains(" on") {
                serviceHasProxy = true
            }
        }
        if let current, serviceHasProxy, !enabled.contains(current) {
            enabled.append(current)
        }
        snap.proxyEnabledServices = enabled
    }

    static func applyVpn(_ body: String, into snap: inout ConnectivitySnapshot) {
        if let line = body.split(whereSeparator: \.isNewline)
            .map(String.init)
            .first(where: { $0.hasPrefix("VPN-like interfaces:") })
        {
            let value = valueAfterColon(line) ?? ""
            snap.vpnLikeInterfaces = value
                .split(separator: ",")
                .map { $0.trimmingCharacters(in: .whitespaces) }
                .filter { !$0.isEmpty && $0 != "—" }
        }
        snap.pathUsesVpn = body.localizedCaseInsensitiveContains("Path appears to use VPN iface: yes")
    }

    static func applyHosts(_ body: String, into snap: inout ConnectivitySnapshot) {
        if let range = body.range(of: "Possibly surprising overrides:") {
            let rest = body[range.upperBound...]
            let count = rest.split(whereSeparator: \.isNewline)
                .map { $0.trimmingCharacters(in: .whitespaces) }
                .filter { $0.hasPrefix("127.") || $0.hasPrefix("::") || $0.contains(".") }
                .count
            snap.hostsOverrideCount = count
            snap.hostsOverrideSummary = String(rest).trimmingCharacters(in: .whitespacesAndNewlines)
        } else if body.localizedCaseInsensitiveContains("surprising") {
            snap.hostsOverrideCount = 1
        }
    }

    static func applyWifi(_ body: String, into snap: inout ConnectivitySnapshot) {
        for raw in body.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            if line.hasPrefix("SSID:") {
                let value = valueAfterColon(line) ?? ""
                snap.wifiSSID = value
                snap.wifiAssociated = !value.localizedCaseInsensitiveContains("unavailable")
                    && !value.localizedCaseInsensitiveContains("not associated")
                    && value != "?"
            }
        }
        if body.localizedCaseInsensitiveContains("No Wi‑Fi interface")
            || body.localizedCaseInsensitiveContains("No Wi-Fi interface")
        {
            snap.wifiAssociated = false
        }
    }

    static func applyCaptive(_ report: DiagnosticReport, into snap: inout ConnectivitySnapshot) {
        snap.captiveStatus = statusCode(from: report.body)
        if let final = report.body.split(whereSeparator: \.isNewline)
            .map(String.init)
            .first(where: { $0.hasPrefix("Final URL:") })
        {
            snap.captiveFinalURL = valueAfterColon(final)
        }
        let status = snap.captiveStatus
        let final = snap.captiveFinalURL ?? ""
        let failed = report.body.localizedCaseInsensitiveContains("Request failed")
        let redirectedOffApple = !final.isEmpty
            && !final.localizedCaseInsensitiveContains("captive.apple.com")
            && !final.localizedCaseInsensitiveContains("apple.com")
        let badStatus = status.map { $0 != 200 && $0 != 204 } ?? failed
        // Classic portal: redirect away from Apple, or non-success without clean 200.
        snap.captiveLikely = redirectedOffApple || (badStatus && snap.pathSatisfied != false)
        if status == 200, final.localizedCaseInsensitiveContains("captive.apple.com") {
            // Likely clear — Apple captive endpoint returned OK on-host.
            snap.captiveLikely = false
        }
    }

    // MARK: - Small parsers

    static func dnsLookupSucceeded(_ body: String) -> Bool {
        let a = sectionLines(body, after: "A:")
        let aaaa = sectionLines(body, after: "AAAA:")
        let aOk = a.contains { looksLikeIP($0) }
        let aaaaOk = aaaa.contains { looksLikeIP($0) }
        return aOk || aaaaOk
    }

    private static func sectionLines(_ body: String, after header: String) -> [String] {
        let lines = body.split(whereSeparator: \.isNewline).map(String.init)
        guard let idx = lines.firstIndex(where: { $0.trimmingCharacters(in: .whitespaces) == header })
        else { return [] }
        var out: [String] = []
        for line in lines[(idx + 1)...] {
            let t = line.trimmingCharacters(in: .whitespaces)
            if t.hasSuffix(":"), !t.contains(" ") { break }
            if t.isEmpty { break }
            out.append(t)
        }
        return out
    }

    private static func looksLikeIP(_ text: String) -> Bool {
        if text == "(none)" { return false }
        if text.contains(":") { return true } // rough IPv6
        let parts = text.split(separator: ".")
        return parts.count == 4 && parts.allSatisfy { UInt8($0) != nil }
    }

    static func statusCode(from body: String) -> Int? {
        for raw in body.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            if line.hasPrefix("Status:") {
                let value = valueAfterColon(line) ?? ""
                return Int(value)
            }
        }
        return nil
    }

    private static func valueAfterColon(_ line: String) -> String? {
        guard let idx = line.firstIndex(of: ":") else { return nil }
        let value = line[line.index(after: idx)...].trimmingCharacters(in: .whitespaces)
        return value.isEmpty ? nil : value
    }

    private static func matchRouteKey(_ text: String, key: String) -> String? {
        for raw in text.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            guard line.lowercased().hasPrefix(key.lowercased()) else { continue }
            if let idx = line.firstIndex(of: ":") {
                let value = line[line.index(after: idx)...].trimmingCharacters(in: .whitespaces)
                if !value.isEmpty { return value }
            } else {
                // `route -n get default` uses "interface: en0" with colon; also "gateway: …"
                let parts = line.split(whereSeparator: \.isWhitespace).map(String.init)
                if parts.count >= 2, parts[0].lowercased().hasPrefix(key.lowercased()) {
                    return parts[1]
                }
            }
        }
        return nil
    }
}
