import Foundation

/// Suggests human-applied remediations from diagnostic text. Never executes them.
enum ProposedFixes {
    static func forDnsConfig(resolvers: [String]) -> [String] {
        var fixes: [String] = []
        if resolvers.isEmpty {
            fixes.append("Open System Settings → Network → Details → DNS and add a resolver (e.g. your router or 1.1.1.1), then retest.")
        }
        if resolvers.contains(where: { $0.hasPrefix("127.") || $0 == "::1" }) {
            fixes.append("A resolver points at localhost — check for a broken local DNS proxy (Docker, VPN, ad-blocker) or remove it from DNS settings.")
        }
        return fixes
    }

    static func forDefaultRoute(interface: String?, gateway: String?, isVpn: Bool) -> [String] {
        var fixes: [String] = []
        if interface == nil && gateway == nil {
            fixes.append("No default route — check Wi‑Fi/Ethernet is connected, or reconnect VPN if you expect one.")
            return fixes
        }
        if isVpn {
            fixes.append("Default route is on a VPN interface (utun/ipsec). If sites fail only while VPN is on: disconnect VPN and retest, or check split-tunnel / DNS settings in the VPN app.")
        }
        return fixes
    }

    static func forPathUnsatisfied() -> [String] {
        [
            "Network path is unsatisfied — enable Wi‑Fi/Ethernet, disable Airplane mode, or check cable/modem.",
            "If a VPN or filter app is installed, quit it temporarily and retest."
        ]
    }

    static func forHostsOverrides(count: Int) -> [String] {
        guard count > 0 else { return [] }
        return [
            "Review surprising `/etc/hosts` overrides (copy the list above). Remove stale lines with care — editing hosts usually needs an admin password in Terminal."
        ]
    }

    static func forProxyEnabled(services: [String]) -> [String] {
        guard !services.isEmpty else { return [] }
        return [
            "HTTP(S)/SOCKS proxy is enabled for: \(services.joined(separator: ", ")). Disable it under System Settings → Network → Details → Proxies if you are not behind a corporate proxy."
        ]
    }

    static func forHttpFailure(statusHint: String) -> [String] {
        var fixes = [
            "Retry after checking DNS and default route (run those toolbox checks).",
            "Try another URL (e.g. https://example.com) to see if the failure is site-specific."
        ]
        if statusHint.localizedCaseInsensitiveContains("captive") || statusHint.contains("530") {
            fixes.insert("Possible captive portal — open http://captive.apple.com/hotspot-detect.html in a browser and complete login.", at: 0)
        }
        return fixes
    }
}
