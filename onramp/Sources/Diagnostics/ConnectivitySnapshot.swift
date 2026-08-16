import Foundation

/// Structured facts for offline “can’t get online” analysis.
/// Pure data — filled by `DiagnosticServices` / playbook runner; ranked by `ConnectivityAnalyzer`.
struct ConnectivitySnapshot: Equatable, Sendable {
    var pathSatisfied: Bool?
    var pathStatusLabel: String?
    var pathExpensive: Bool?
    var pathInterfaces: [String] = []

    var defaultInterface: String?
    var defaultGateway: String?
    var defaultIsVpn: Bool = false
    var hasDefaultRoute: Bool?

    var dnsResolvers: [String] = []
    var dnsSearchDomains: [String] = []

    var proxyEnabledServices: [String] = []
    var vpnLikeInterfaces: [String] = []
    var pathUsesVpn: Bool = false

    var hostsOverrideCount: Int = 0
    var hostsOverrideSummary: String?

    var wifiSSID: String?
    var wifiAssociated: Bool?

    /// example.com A/AAAA lookup produced at least one address.
    var dnsLookupOk: Bool?
    var dnsLookupDetail: String?

    /// TCP 1.1.1.1:443
    var tcpCloudflareOk: Bool?
    /// TCP 8.8.8.8:443 — second IP probe when useful
    var tcpGoogleDnsOk: Bool?

    var httpExampleStatus: Int?
    var httpExampleOk: Bool?
    var httpExampleDetail: String?

    var captiveStatus: Int?
    var captiveFinalURL: String?
    var captiveBodyHint: String?
    var captiveLikely: Bool = false

    var pingLossPercent: Double?
    var pingDetail: String?

    /// Per-check reports for the UI evidence list / copy-all.
    var checkReports: [DiagnosticReport] = []
}

/// Which playbook lens to apply when ranking causes.
enum ConnectivityPlaybookKind: String, CaseIterable, Identifiable, Sendable {
    case cantGetOnline
    case vpnBroken
    case dnsWrong
    case captivePortal
    case someSitesFail

    var id: String { rawValue }

    var title: String {
        switch self {
        case .cantGetOnline: return "Can't get online"
        case .vpnBroken: return "VPN connected but broken"
        case .dnsWrong: return "DNS feels wrong"
        case .captivePortal: return "Captive portal / hotel Wi‑Fi"
        case .someSitesFail: return "Only some sites fail"
        }
    }

    var subtitle: String {
        switch self {
        case .cantGetOnline:
            return "Full offline playbook: path, route, DNS, proxy, VPN, hosts, then live probes"
        case .vpnBroken:
            return "Focus on utun/default route vs DNS split-tunnel mismatches"
        case .dnsWrong:
            return "Focus on resolvers, lookup, and hosts overrides"
        case .captivePortal:
            return "Probe Apple captive URL and HTTP redirects"
        case .someSitesFail:
            return "Separate DNS vs routing vs proxy/VPN vs hosts"
        }
    }

    var symbolName: String {
        switch self {
        case .cantGetOnline: return "wifi.exclamationmark"
        case .vpnBroken: return "lock.shield"
        case .dnsWrong: return "text.magnifyingglass"
        case .captivePortal: return "building.2"
        case .someSitesFail: return "rectangle.stack.badge.minus"
        }
    }
}

struct PlaybookResult: Equatable, Sendable {
    var kind: ConnectivityPlaybookKind
    var triage: TriageReportViewModel
    var checks: [DiagnosticReport]
    var actions: [SuggestedAction]
    var looksOnline: Bool

    var markdown: String {
        var parts = [triage.markdown]
        if !actions.isEmpty {
            parts.append("")
            parts.append("## Suggested actions")
            for (i, action) in actions.enumerated() {
                parts.append("\(i + 1). **\(action.title)** — \(action.why)")
            }
        }
        if !checks.isEmpty {
            parts.append("")
            parts.append("---")
            parts.append("")
            parts.append("## Raw checks")
            for check in checks {
                parts.append("")
                parts.append(check.markdown)
            }
        }
        return parts.joined(separator: "\n")
    }
}
