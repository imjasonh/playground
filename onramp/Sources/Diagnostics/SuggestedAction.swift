import AppKit
import Foundation

/// A concrete next step the user can take from a triage result — Settings link,
/// captive portal, or a confirmed read-only diagnostic command whose output feeds
/// back into another playbook pass.
struct SuggestedAction: Identifiable, Equatable, Sendable {
    enum Kind: Equatable, Sendable {
        /// Opens a System Settings / http(s) URL (no shell).
        case openURL(String)
        /// Runs an allowlisted read-only diagnostic via DiagnosticServices.
        case diagnostic(DiagnosticProbe)
        /// Re-runs the current playbook with fresh probes.
        case recheck
    }

    /// Allowlisted probes the UI may run after an explicit click.
    enum DiagnosticProbe: String, Equatable, Sendable, CaseIterable {
        case pathStatus
        case defaultRoute
        case dnsConfig
        case dnsLookupExample
        case pingCloudflare
        case reachabilityCloudflare
        case httpExample
        case captivePortal
        case proxyConfig
        case vpnInterfaces
        case hostsFile

        var title: String {
            switch self {
            case .pathStatus: return "Re-check network path"
            case .defaultRoute: return "Re-check default route"
            case .dnsConfig: return "Re-check DNS config"
            case .dnsLookupExample: return "Look up example.com"
            case .pingCloudflare: return "Ping 1.1.1.1"
            case .reachabilityCloudflare: return "TCP probe 1.1.1.1:443"
            case .httpExample: return "HTTPS probe example.com"
            case .captivePortal: return "Captive portal probe"
            case .proxyConfig: return "Re-check proxy settings"
            case .vpnInterfaces: return "Re-check VPN interfaces"
            case .hostsFile: return "Re-check /etc/hosts"
            }
        }

        /// Human-readable command / API summary for the confirm sheet.
        var commandSummary: String {
            switch self {
            case .pathStatus: return "NWPathMonitor snapshot (read-only)"
            case .defaultRoute: return "/sbin/route -n get default"
            case .dnsConfig: return "/usr/sbin/scutil --dns"
            case .dnsLookupExample: return "/usr/bin/dig +short A/AAAA example.com"
            case .pingCloudflare: return "/sbin/ping -c 4 -t 8 1.1.1.1"
            case .reachabilityCloudflare: return "NWConnection TCP 1.1.1.1:443"
            case .httpExample: return "HTTPS GET https://example.com"
            case .captivePortal: return "HTTP GET http://captive.apple.com/hotspot-detect.html"
            case .proxyConfig: return "/usr/sbin/networksetup -get*proxy …"
            case .vpnInterfaces: return "Enumerate utun/ipsec + path interfaces"
            case .hostsFile: return "Read /etc/hosts"
            }
        }
    }

    var id: String
    var title: String
    /// Why this step is suggested for the current diagnosis.
    var why: String
    /// Plain-language description of what the button will do.
    var whatItDoes: String
    var kind: Kind

    var confirmationDetail: String {
        switch kind {
        case .openURL(let s):
            return "Opens:\n\(s)"
        case .diagnostic(let probe):
            return "Runs (read-only):\n\(probe.commandSummary)"
        case .recheck:
            return "Re-runs the full Can’t get online playbook with fresh probes. Nothing is changed on your Mac."
        }
    }

    var isReadOnly: Bool {
        switch kind {
        case .openURL, .diagnostic, .recheck: return true
        }
    }
}

enum SuggestedActionBuilder {
    static func actions(
        for findings: [ConnectivityAnalyzer.Finding],
        snapshot: ConnectivitySnapshot,
        kind: ConnectivityPlaybookKind
    ) -> [SuggestedAction] {
        var out: [SuggestedAction] = []
        let codes = Set(findings.prefix(4).map(\.code))

        func add(_ action: SuggestedAction) {
            guard !out.contains(where: { $0.id == action.id }) else { return }
            out.append(action)
        }

        if codes.contains(.noPath) || codes.contains(.noDefaultRoute) || codes.contains(.wifiUnknown) {
            add(
                SuggestedAction(
                    id: "open-network",
                    title: "Open Network settings",
                    why: "Wi‑Fi/Ethernet may be disconnected or have no default route.",
                    whatItDoes: "Opens System Settings → Network so you can connect or pick an interface.",
                    kind: .openURL(SettingsDeepLinks.networkURLString)
                )
            )
            add(
                SuggestedAction(
                    id: "recheck-path",
                    title: "Re-check path + route",
                    why: "After you reconnect, confirm the Mac has a usable path.",
                    whatItDoes: "Runs a fresh path status check (read-only).",
                    kind: .diagnostic(.pathStatus)
                )
            )
        }

        if codes.contains(.captivePortal) {
            add(
                SuggestedAction(
                    id: "open-captive",
                    title: "Open captive portal login",
                    why: "Hotel/cafe Wi‑Fi often blocks the Internet until you accept terms in a browser.",
                    whatItDoes: "Opens Apple’s captive detection URL in your default browser.",
                    kind: .openURL("http://captive.apple.com/hotspot-detect.html")
                )
            )
            add(
                SuggestedAction(
                    id: "probe-captive",
                    title: "Re-test captive portal",
                    why: "After login, verify the portal probe returns a clean success.",
                    whatItDoes: "HTTP GET captive.apple.com (read-only).",
                    kind: .diagnostic(.captivePortal)
                )
            )
        }

        if codes.contains(.proxyBlocking) {
            add(
                SuggestedAction(
                    id: "open-proxies",
                    title: "Open Proxy settings",
                    why: "A leftover HTTP/HTTPS/SOCKS proxy commonly breaks browsing off the corporate network.",
                    whatItDoes: "Opens System Settings → Network → Proxies.",
                    kind: .openURL(SettingsDeepLinks.proxiesURLString)
                )
            )
            add(
                SuggestedAction(
                    id: "recheck-proxy",
                    title: "Re-check proxies",
                    why: "Confirm proxies are off after you change Settings.",
                    whatItDoes: "Reads networksetup proxy flags (read-only).",
                    kind: .diagnostic(.proxyConfig)
                )
            )
        }

        if codes.contains(.vpnPath) {
            add(
                SuggestedAction(
                    id: "recheck-vpn",
                    title: "Re-check VPN path",
                    why: "After disconnecting VPN, confirm traffic is no longer forced through utun.",
                    whatItDoes: "Re-reads VPN-like interfaces vs the current path (read-only).",
                    kind: .diagnostic(.vpnInterfaces)
                )
            )
            add(
                SuggestedAction(
                    id: "recheck-route-vpn",
                    title: "Re-check default route",
                    why: "See whether the default route left the VPN interface.",
                    whatItDoes: "Runs route get default (read-only).",
                    kind: .diagnostic(.defaultRoute)
                )
            )
        }

        if codes.contains(.dnsEmpty) || codes.contains(.dnsLocalhost) || codes.contains(.dnsLookupFailed) {
            add(
                SuggestedAction(
                    id: "open-dns",
                    title: "Open DNS settings",
                    why: "Resolvers are missing, point at localhost, or lookups are failing.",
                    whatItDoes: "Opens System Settings → Network → DNS.",
                    kind: .openURL(SettingsDeepLinks.dnsURLString)
                )
            )
            add(
                SuggestedAction(
                    id: "dig-example",
                    title: "Look up example.com",
                    why: "Fresh evidence for whether names resolve after you change DNS.",
                    whatItDoes: "Runs dig A/AAAA for example.com (read-only).",
                    kind: .diagnostic(.dnsLookupExample)
                )
            )
            add(
                SuggestedAction(
                    id: "recheck-dns-config",
                    title: "Re-check DNS config",
                    why: "Confirm resolvers after editing Settings.",
                    whatItDoes: "Runs scutil --dns (read-only).",
                    kind: .diagnostic(.dnsConfig)
                )
            )
        }

        if codes.contains(.dnsOkTcpFail) || codes.contains(.partialFailure) {
            add(
                SuggestedAction(
                    id: "ping-cf",
                    title: "Ping 1.1.1.1",
                    why: "Separate ICMP reachability from DNS/HTTPS failures.",
                    whatItDoes: "Runs ping -c 4 1.1.1.1 (read-only).",
                    kind: .diagnostic(.pingCloudflare)
                )
            )
            add(
                SuggestedAction(
                    id: "tcp-cf",
                    title: "TCP probe 1.1.1.1:443",
                    why: "Some networks block ICMP; TCP 443 is a better Internet check.",
                    whatItDoes: "Opens a short TCP connection to 1.1.1.1:443 (read-only).",
                    kind: .diagnostic(.reachabilityCloudflare)
                )
            )
            add(
                SuggestedAction(
                    id: "http-example",
                    title: "HTTPS probe example.com",
                    why: "Confirm whether browsers would succeed for a known site.",
                    whatItDoes: "HTTPS GET https://example.com (read-only).",
                    kind: .diagnostic(.httpExample)
                )
            )
        }

        if codes.contains(.hostsOverrides) {
            add(
                SuggestedAction(
                    id: "recheck-hosts",
                    title: "Re-read hosts file",
                    why: "Surprising /etc/hosts overrides can break only some names.",
                    whatItDoes: "Reads /etc/hosts (read-only).",
                    kind: .diagnostic(.hostsFile)
                )
            )
        }

        // Always offer a full recheck unless already healthy.
        if !ConnectivityAnalyzer.looksHealthy(snapshot) || kind != .cantGetOnline {
            add(
                SuggestedAction(
                    id: "recheck-full",
                    title: "Re-run full diagnosis",
                    why: "After you change Wi‑Fi, VPN, DNS, or proxies, gather fresh evidence.",
                    whatItDoes: "Runs the full playbook again (read-only probes only).",
                    kind: .recheck
                )
            )
        }

        return Array(out.prefix(8))
    }
}

extension SettingsDeepLinks {
    static var networkURLString: String {
        "x-apple.systempreferences:com.apple.Network-Settings.extension"
    }

    static var dnsURLString: String {
        "x-apple.systempreferences:com.apple.Network-Settings.extension?DNS"
    }

    static var proxiesURLString: String {
        "x-apple.systempreferences:com.apple.Network-Settings.extension?Proxies"
    }
}

/// Executes a suggested action after the user confirms. Diagnostics stay read-only.
enum SuggestedActionRunner {
    struct Result: Equatable, Sendable {
        var title: String
        var body: String
        var shouldRecheck: Bool
    }

    static func run(
        _ action: SuggestedAction,
        services: DiagnosticServices = .shared
    ) async -> Result {
        switch action.kind {
        case .openURL(let string):
            if let url = URL(string: string) {
                await MainActor.run {
                    NSWorkspace.shared.open(url)
                }
            }
            return Result(
                title: action.title,
                body: "Opened \(string).\n\nWhen you’re done there, run “Re-run full diagnosis” to see what changed.",
                shouldRecheck: false
            )
        case .recheck:
            return Result(
                title: action.title,
                body: "Ready to re-run the playbook.",
                shouldRecheck: true
            )
        case .diagnostic(let probe):
            let report = await runProbe(probe, services: services)
            return Result(
                title: report.title,
                body: report.markdown,
                shouldRecheck: true
            )
        }
    }

    private static func runProbe(
        _ probe: SuggestedAction.DiagnosticProbe,
        services: DiagnosticServices
    ) async -> DiagnosticReport {
        switch probe {
        case .pathStatus: return await services.pathStatus()
        case .defaultRoute: return await services.defaultRoute()
        case .dnsConfig: return await services.dnsConfig()
        case .dnsLookupExample: return await services.dnsLookup(hostname: "example.com")
        case .pingCloudflare: return await services.ping(host: "1.1.1.1")
        case .reachabilityCloudflare: return await services.reachability(host: "1.1.1.1", port: 443)
        case .httpExample: return await services.httpProbe(urlString: "https://example.com")
        case .captivePortal:
            return await services.httpProbe(urlString: "http://captive.apple.com/hotspot-detect.html")
        case .proxyConfig: return await services.proxyConfig()
        case .vpnInterfaces: return await services.vpnInterfaces()
        case .hostsFile: return await services.hostsFile()
        }
    }
}
