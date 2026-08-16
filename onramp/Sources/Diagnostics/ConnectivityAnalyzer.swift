import Foundation

/// Ranks likely causes from a `ConnectivitySnapshot` without calling the network.
/// Used by playbooks (Toolbox / menu bar) so “can't get online” works without Apple Intelligence.
enum ConnectivityAnalyzer {
    struct Outcome: Equatable, Sendable {
        var report: TriageReportViewModel
        var actions: [SuggestedAction]
        var looksOnline: Bool
    }

    static func analyze(
        _ snapshot: ConnectivitySnapshot,
        kind: ConnectivityPlaybookKind = .cantGetOnline
    ) -> Outcome {
        let findings = collectFindings(snapshot)
        let ranked = rank(findings, kind: kind, snapshot: snapshot)
        let primary = ranked.first
        let evidence = evidenceBullets(snapshot: snapshot, findings: ranked)
        let steps = proposedSteps(for: ranked, snapshot: snapshot, kind: kind)
        let actions = SuggestedActionBuilder.actions(for: ranked, snapshot: snapshot, kind: kind)
        let online = looksHealthy(snapshot)

        let headline: String
        let likelyCause: String
        if online {
            headline = "You're online"
            likelyCause =
                "Path, DNS, and probes succeeded. If a specific site still fails, try “Only some sites fail” — otherwise you’re done."
        } else if let primary {
            headline = primary.headline
            likelyCause = primary.detail
        } else {
            headline = "Couldn’t pinpoint a single cause"
            likelyCause =
                "Some checks were inconclusive. Try the suggested steps below, then re-run diagnosis."
        }

        let report = TriageReportViewModel(
            headline: headline,
            likelyCause: likelyCause,
            evidence: evidence,
            proposedSteps: steps
        )
        return Outcome(report: report, actions: actions, looksOnline: online)
    }

    // MARK: - Findings

    struct Finding: Equatable {
        enum Code: String, Equatable {
            case noPath
            case noDefaultRoute
            case captivePortal
            case proxyBlocking
            case vpnPath
            case dnsEmpty
            case dnsLocalhost
            case dnsLookupFailed
            case dnsOkTcpFail
            case hostsOverrides
            case partialFailure
            case wifiUnknown
        }

        var code: Code
        var severity: Int // higher = more urgent / more specific
        var headline: String
        var detail: String
    }

    static func collectFindings(_ s: ConnectivitySnapshot) -> [Finding] {
        var out: [Finding] = []

        if s.pathSatisfied == false {
            out.append(
                Finding(
                    code: .noPath,
                    severity: 100,
                    headline: "No usable network path",
                    detail:
                        "NWPathMonitor reports the path as \(s.pathStatusLabel ?? "unsatisfied"). Wi‑Fi/Ethernet may be off, disconnected, or blocked before routing/DNS matter."
                )
            )
        }

        if s.hasDefaultRoute == false {
            out.append(
                Finding(
                    code: .noDefaultRoute,
                    severity: 95,
                    headline: "No default route",
                    detail:
                        "This Mac has no default gateway. Traffic can’t leave the local link until Wi‑Fi/Ethernet reconnects or a VPN provides a route."
                )
            )
        }

        if s.captiveLikely {
            out.append(
                Finding(
                    code: .captivePortal,
                    severity: 90,
                    headline: "Likely captive portal",
                    detail:
                        "The captive probe didn’t get a clean Internet success (status \(s.captiveStatus.map(String.init) ?? "?"), final URL \(s.captiveFinalURL ?? "n/a")). Hotel/cafe Wi‑Fi often requires a browser login first."
                )
            )
        }

        if !s.proxyEnabledServices.isEmpty, hasOutboundTrouble(s) {
            out.append(
                Finding(
                    code: .proxyBlocking,
                    severity: 85,
                    headline: "System proxy enabled",
                    detail:
                        "HTTP(S)/SOCKS proxy is on for: \(s.proxyEnabledServices.joined(separator: ", ")). A stale corporate or leftover proxy commonly breaks browsing off that network."
                )
            )
        }

        if (s.defaultIsVpn || s.pathUsesVpn), hasOutboundTrouble(s) {
            out.append(
                Finding(
                    code: .vpnPath,
                    severity: 80,
                    headline: "Traffic going through VPN",
                    detail:
                        "Default route/path uses a VPN-like interface (\(s.defaultInterface ?? s.pathInterfaces.joined(separator: ", "))). If sites fail only with VPN up, disconnect or fix split-tunnel/DNS in the VPN app."
                )
            )
        }

        if s.dnsResolvers.isEmpty {
            out.append(
                Finding(
                    code: .dnsEmpty,
                    severity: 75,
                    headline: "No DNS resolvers configured",
                    detail: "scutil didn’t list any nameservers. Browsers can’t resolve names until DNS is set."
                )
            )
        } else if s.dnsResolvers.contains(where: { $0.hasPrefix("127.") || $0 == "::1" }) {
            out.append(
                Finding(
                    code: .dnsLocalhost,
                    severity: 74,
                    headline: "DNS points at localhost",
                    detail:
                        "A resolver is \(s.dnsResolvers.first(where: { $0.hasPrefix("127.") || $0 == "::1" }) ?? "127.0.0.1") — often a dead local DNS proxy (VPN, Docker, ad-blocker)."
                )
            )
        }

        if s.dnsLookupOk == false {
            let tcpOk = s.tcpCloudflareOk == true || s.tcpGoogleDnsOk == true
            if tcpOk {
                out.append(
                    Finding(
                        code: .dnsLookupFailed,
                        severity: 72,
                        headline: "DNS lookup failed (routing may be fine)",
                        detail:
                            "Couldn’t resolve a test hostname, but TCP to a public IP worked. That pattern usually means DNS config — not the Wi‑Fi radio."
                    )
                )
            } else {
                out.append(
                    Finding(
                        code: .dnsLookupFailed,
                        severity: 70,
                        headline: "DNS lookup failed",
                        detail:
                            "No addresses returned for the test hostname. Check DNS config, VPN DNS, or try again after reconnecting."
                    )
                )
            }
        }

        if s.dnsLookupOk == true, s.tcpCloudflareOk == false, s.httpExampleOk == false {
            out.append(
                Finding(
                    code: .dnsOkTcpFail,
                    severity: 68,
                    headline: "Names resolve but connections fail",
                    detail:
                        "DNS worked, but TCP/HTTPS probes failed. Suspect firewall, VPN filter, or upstream outage rather than resolver settings."
                )
            )
        }

        if s.hostsOverrideCount > 0 {
            out.append(
                Finding(
                    code: .hostsOverrides,
                    severity: 55,
                    headline: "Custom /etc/hosts overrides",
                    detail:
                        "\(s.hostsOverrideCount) surprising hosts mapping(s). Stale overrides can make “only some sites” fail while the rest of the Internet works."
                )
            )
        }

        if s.wifiAssociated == false, s.pathSatisfied != true {
            out.append(
                Finding(
                    code: .wifiUnknown,
                    severity: 40,
                    headline: "Wi‑Fi association unclear",
                    detail:
                        "Couldn’t read a Wi‑Fi SSID (Location permission or not associated). Confirm Wi‑Fi is joined under System Settings → Network."
                )
            )
        }

        if isPartial(s) {
            out.append(
                Finding(
                    code: .partialFailure,
                    severity: 50,
                    headline: "Mixed probe results",
                    detail:
                        "Some probes succeeded and others failed — typical of split DNS, proxy, VPN, or hosts-file issues rather than a total outage."
                )
            )
        }

        return out
    }

    static func rank(
        _ findings: [Finding],
        kind: ConnectivityPlaybookKind,
        snapshot _: ConnectivitySnapshot
    ) -> [Finding] {
        let boosted = findings.map { finding -> Finding in
            var f = finding
            f.severity += kindBoost(finding.code, kind: kind)
            return f
        }
        return boosted.sorted { lhs, rhs in
            if lhs.severity != rhs.severity { return lhs.severity > rhs.severity }
            return lhs.code.rawValue < rhs.code.rawValue
        }
    }

    private static func kindBoost(_ code: Finding.Code, kind: ConnectivityPlaybookKind) -> Int {
        switch kind {
        case .cantGetOnline:
            return 0
        case .vpnBroken:
            return code == .vpnPath ? 20 : 0
        case .dnsWrong:
            return [.dnsEmpty, .dnsLocalhost, .dnsLookupFailed, .hostsOverrides].contains(code) ? 20 : 0
        case .captivePortal:
            return code == .captivePortal ? 25 : 0
        case .someSitesFail:
            return [.hostsOverrides, .dnsLookupFailed, .proxyBlocking, .vpnPath, .partialFailure]
                .contains(code) ? 15 : 0
        }
    }

    // MARK: - Evidence & steps

    static func evidenceBullets(snapshot s: ConnectivitySnapshot, findings: [Finding]) -> [String] {
        var bullets: [String] = []
        if let label = s.pathStatusLabel {
            let ifaces = s.pathInterfaces.isEmpty ? "—" : s.pathInterfaces.joined(separator: ", ")
            bullets.append("path_status: \(label); interfaces \(ifaces)")
        }
        if let iface = s.defaultInterface ?? nil {
            let gw = s.defaultGateway ?? "?"
            bullets.append(
                "default_route: iface \(iface), gateway \(gw)\(s.defaultIsVpn ? " (VPN-like)" : "")"
            )
        } else if s.hasDefaultRoute == false {
            bullets.append("default_route: none")
        }
        if s.dnsResolvers.isEmpty {
            bullets.append("dns_config: no resolvers")
        } else {
            bullets.append("dns_config: \(s.dnsResolvers.prefix(4).joined(separator: ", "))")
        }
        if !s.proxyEnabledServices.isEmpty {
            bullets.append("proxy_config: enabled on \(s.proxyEnabledServices.joined(separator: ", "))")
        }
        if s.pathUsesVpn || !s.vpnLikeInterfaces.isEmpty {
            bullets.append(
                "vpn_interfaces: \(s.vpnLikeInterfaces.joined(separator: ", ")); path uses VPN: \(s.pathUsesVpn ? "yes" : "no")"
            )
        }
        if s.hostsOverrideCount > 0 {
            bullets.append("hosts_file: \(s.hostsOverrideCount) surprising override(s)")
        }
        if let ssid = s.wifiSSID {
            bullets.append("current_wifi: \(ssid)")
        }
        if let dns = s.dnsLookupOk {
            bullets.append("dns_lookup: \(dns ? "ok" : "failed")")
        }
        if let tcp = s.tcpCloudflareOk {
            bullets.append("reachability 1.1.1.1:443: \(tcp ? "ok" : "failed")")
        }
        if let http = s.httpExampleOk {
            bullets.append(
                "http_probe example.com: \(http ? "ok" : "failed")\(s.httpExampleStatus.map { " (HTTP \($0))" } ?? "")"
            )
        }
        if s.captiveStatus != nil || s.captiveLikely {
            bullets.append(
                "captive probe: status \(s.captiveStatus.map(String.init) ?? "?"); likely portal: \(s.captiveLikely ? "yes" : "no")"
            )
        }
        if let loss = s.pingLossPercent {
            bullets.append(String(format: "ping: %.0f%% loss", loss))
        }
        // Cap evidence; prefer finding headlines if we somehow have nothing.
        if bullets.isEmpty {
            bullets = findings.prefix(5).map(\.headline)
        }
        return Array(bullets.prefix(10))
    }

    static func proposedSteps(
        for findings: [Finding],
        snapshot: ConnectivitySnapshot,
        kind: ConnectivityPlaybookKind
    ) -> [String] {
        var steps: [String] = []
        let codes = Set(findings.prefix(4).map(\.code))

        if codes.contains(.noPath) || codes.contains(.noDefaultRoute) {
            steps.append(
                "Open System Settings → Network and make sure Wi‑Fi or Ethernet is connected (not “Not Connected”)."
            )
            steps.append("Toggle Wi‑Fi off and on, or join a different network, then re-run this playbook.")
        }
        if codes.contains(.captivePortal) {
            steps.append(
                "Open http://captive.apple.com/hotspot-detect.html in Safari and complete the login/accept page."
            )
            steps.append("After login succeeds, re-run Can’t get online to confirm DNS and HTTPS work.")
        }
        if codes.contains(.proxyBlocking) {
            steps.append(
                "Open System Settings → Network → Details… → Proxies and disable HTTP/HTTPS/SOCKS unless you need a corporate proxy."
            )
        }
        if codes.contains(.vpnPath) {
            steps.append("Disconnect the VPN (menu bar VPN/app), then retest a website.")
            steps.append(
                "If you need the VPN, check its app for split-tunnel / DNS settings, or try a different VPN server."
            )
        }
        if codes.contains(.dnsEmpty) || codes.contains(.dnsLocalhost) || codes.contains(.dnsLookupFailed) {
            steps.append(
                "Open System Settings → Network → Details… → DNS. Remove 127.0.0.1 if present, or set resolvers to your router and/or 1.1.1.1, then retest."
            )
        }
        if codes.contains(.hostsOverrides) {
            steps.append(
                "Review surprising /etc/hosts lines (see raw Hosts file check). Remove stale overrides carefully — editing hosts usually needs an admin password."
            )
        }
        if codes.contains(.dnsOkTcpFail) {
            steps.append("Temporarily quit firewall/filter apps (Little Snitch, corporate agents) and retest.")
            steps.append("If only VPN is up, disconnect VPN and compare.")
        }
        if codes.contains(.wifiUnknown), !codes.contains(.noPath) {
            steps.append("Confirm you are joined to Wi‑Fi under System Settings → Network (grant Location if you want SSID shown here).")
        }

        // Kind-specific nudge when findings were thin.
        if steps.isEmpty {
            switch kind {
            case .cantGetOnline:
                if looksHealthy(snapshot) {
                    return []
                }
                steps.append("Reconnect Wi‑Fi/Ethernet, then re-run Can’t get online.")
            case .vpnBroken:
                steps.append("Disconnect VPN and compare; if fixed, adjust VPN DNS/split-tunnel.")
            case .dnsWrong:
                steps.append("Set DNS to your router or 1.1.1.1 under System Settings → Network → Details… → DNS.")
            case .captivePortal:
                steps.append("Open http://captive.apple.com/hotspot-detect.html and complete login.")
            case .someSitesFail:
                steps.append("Compare failing vs working URLs with DNS lookup and HTTP probe in the Toolbox.")
            }
        }

        // Dedupe while preserving order.
        var seen = Set<String>()
        return steps.filter { seen.insert($0).inserted }
    }

    // MARK: - Helpers

    static func looksHealthy(_ s: ConnectivitySnapshot) -> Bool {
        s.pathSatisfied == true
            && s.hasDefaultRoute != false
            && s.dnsLookupOk == true
            && (s.tcpCloudflareOk == true || s.httpExampleOk == true)
            && !s.captiveLikely
    }

    static func hasOutboundTrouble(_ s: ConnectivitySnapshot) -> Bool {
        s.dnsLookupOk == false
            || s.tcpCloudflareOk == false
            || s.httpExampleOk == false
            || s.captiveLikely
            || s.pathSatisfied == false
    }

    static func isPartial(_ s: ConnectivitySnapshot) -> Bool {
        let flags: [Bool?] = [s.dnsLookupOk, s.tcpCloudflareOk, s.httpExampleOk]
        let known = flags.compactMap { $0 }
        guard known.count >= 2 else { return false }
        return known.contains(true) && known.contains(false)
    }
}
