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
    case processUsage
    case topMemory
    case topCPU
    case diskSpace
    case memoryPressure
    case systemLoad
    case powerAssertions
    case listeningPorts
    case crashReports
    case loginItems
    case userStorage
    case batteryPower

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
        case .processUsage: return "Process usage"
        case .topMemory: return "Top memory"
        case .topCPU: return "Top CPU"
        case .diskSpace: return "Disk space"
        case .memoryPressure: return "Memory pressure"
        case .systemLoad: return "System load"
        case .powerAssertions: return "Power assertions"
        case .listeningPorts: return "Listening ports"
        case .crashReports: return "Crash reports"
        case .loginItems: return "Login / launch agents"
        case .userStorage: return "User storage hotspots"
        case .batteryPower: return "Battery / power"
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
        case .processUsage: return "CPU/memory for a named app"
        case .topMemory: return "Highest RSS processes"
        case .topCPU: return "Hottest CPU processes"
        case .diskSpace: return "Free space on volumes"
        case .memoryPressure: return "vm_stat snapshot"
        case .systemLoad: return "Load average + uptime"
        case .powerAssertions: return "What blocks sleep"
        case .listeningPorts: return "TCP listen / port conflicts"
        case .crashReports: return "Recent DiagnosticReports"
        case .loginItems: return "LaunchAgents / Daemons plists"
        case .userStorage: return "Downloads, Caches, and friends"
        case .batteryPower: return "AC vs battery (pmset)"
        }
    }

    var needsHostField: Bool {
        switch self {
        case .dnsLookup, .reachability, .httpProbe, .processUsage, .listeningPorts, .crashReports:
            return true
        default:
            return false
        }
    }

    var hostPlaceholder: String {
        switch self {
        case .dnsLookup: return "example.com"
        case .reachability: return "1.1.1.1"
        case .httpProbe: return "https://example.com"
        case .processUsage: return "Cursor"
        case .listeningPorts: return "3000 (optional port)"
        case .crashReports: return "App name (optional)"
        default: return ""
        }
    }

    var defaultHost: String {
        switch self {
        case .dnsLookup: return "example.com"
        case .reachability: return "1.1.1.1"
        case .httpProbe: return "https://example.com"
        case .processUsage: return "Cursor"
        case .listeningPorts: return ""
        case .crashReports: return ""
        default: return ""
        }
    }
}
