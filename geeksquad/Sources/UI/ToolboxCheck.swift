import Foundation

enum ToolboxCheck: String, CaseIterable, Identifiable, Hashable {
    case interfaces
    case defaultRoute
    case pathStatus
    case dnsConfig
    case dnsLookup
    case reachability
    case httpProbe
    case proxyConfig
    case vpnInterfaces
    case hostsFile
    case currentWifi

    var id: String { rawValue }

    var title: String {
        switch self {
        case .interfaces: return "Interfaces"
        case .defaultRoute: return "Default route"
        case .pathStatus: return "Path status"
        case .dnsConfig: return "DNS config"
        case .dnsLookup: return "DNS lookup"
        case .reachability: return "Reachability"
        case .httpProbe: return "HTTP probe"
        case .proxyConfig: return "Proxy config"
        case .vpnInterfaces: return "VPN interfaces"
        case .hostsFile: return "Hosts file"
        case .currentWifi: return "Current Wi‑Fi"
        }
    }

    var subtitle: String {
        switch self {
        case .interfaces: return "Addresses and VPN-like ifaces"
        case .defaultRoute: return "Gateway and interface"
        case .pathStatus: return "NWPathMonitor snapshot"
        case .dnsConfig: return "Resolvers (scutil --dns)"
        case .dnsLookup: return "A/AAAA via dig"
        case .reachability: return "TCP connect"
        case .httpProbe: return "GET timing and status"
        case .proxyConfig: return "System HTTP/HTTPS/SOCKS"
        case .vpnInterfaces: return "utun/ipsec vs path"
        case .hostsFile: return "/etc/hosts overrides"
        case .currentWifi: return "SSID if Location allows"
        }
    }

    var needsHostField: Bool {
        self == .dnsLookup || self == .reachability || self == .httpProbe
    }

    var hostPlaceholder: String {
        switch self {
        case .dnsLookup: return "example.com"
        case .reachability: return "1.1.1.1"
        case .httpProbe: return "https://example.com"
        default: return ""
        }
    }

    var defaultHost: String {
        switch self {
        case .dnsLookup: return "example.com"
        case .reachability: return "1.1.1.1"
        case .httpProbe: return "https://example.com"
        default: return ""
        }
    }
}
