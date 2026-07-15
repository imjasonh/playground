import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Shared triage system prompt for the on-device model.
enum TriageInstructions {
    static let text = """
        You are Geek Squad, an offline Mac network and configuration technician.
        The user describes what they see and what they want fixed.

        Rules:
        - Use diagnostic tools to gather facts before concluding. Prefer path_status, \
        default_route, dns_config, and interfaces early; then dig deeper (dns_lookup, \
        reachability, http_probe, proxy_config, vpn_interfaces, hosts_file, current_wifi).
        - Never invent IP addresses, DNS results, routes, or proxy settings — only cite \
        tool output.
        - Propose clear, numbered steps the user can take themselves. Do not claim you \
        changed System Settings, ran sudo, or applied a fix.
        - Be concise and practical. Lead with the likely cause, then evidence, then \
        proposed fixes.
        - If a tool fails or returns empty, say so and try another angle.
        """
}

#if canImport(FoundationModels)

/// Notifies the UI when a diagnostic tool runs (so the chat can show activity).
@available(macOS 26.0, *)
final class ToolActivityHub: @unchecked Sendable {
    private let handler: @Sendable (String) -> Void

    init(handler: @escaping @Sendable (String) -> Void) {
        self.handler = handler
    }

    func note(_ name: String) {
        handler(name)
    }
}

@available(macOS 26.0, *)
struct InterfacesTool: Tool {
    let name = "interfaces"
    let description = "List network interfaces with addresses; note VPN-like utun/ipsec/ppp interfaces."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Optional focus; use empty string if none")
        var note: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.interfaces()
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct DefaultRouteTool: Tool {
    let name = "default_route"
    let description = "Show the Mac's default route (gateway and interface), including whether traffic exits via VPN."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Optional focus; use empty string if none")
        var note: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.defaultRoute()
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct PathStatusTool: Tool {
    let name = "path_status"
    let description = "Snapshot of NWPathMonitor: satisfied/unsatisfied, expensive, constrained, interfaces, IP/DNS support."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Optional focus; use empty string if none")
        var note: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.pathStatus()
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct DnsConfigTool: Tool {
    let name = "dns_config"
    let description = "Summarize configured DNS resolvers and search domains (from scutil --dns)."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Optional focus; use empty string if none")
        var note: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.dnsConfig()
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct DnsLookupTool: Tool {
    let name = "dns_lookup"
    let description = "Resolve A and AAAA records for a hostname using dig."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Hostname to resolve, e.g. example.com")
        var hostname: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.dnsLookup(hostname: arguments.hostname)
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct ReachabilityTool: Tool {
    let name = "reachability"
    let description = "Try a TCP connect to host:port (useful to separate DNS failure from routing/firewall)."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Host name or IP")
        var host: String
        @Guide(description: "TCP port number, typically 443 or 80")
        var port: Int
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let port = UInt16(clamping: arguments.port)
        let report = await DiagnosticServices.shared.reachability(host: arguments.host, port: port)
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct HttpProbeTool: Tool {
    let name = "http_probe"
    let description = "HTTP(S) GET a URL; report status, redirects, timing, and errors (captive portals, TLS)."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Full http or https URL")
        var url: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.httpProbe(urlString: arguments.url)
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct ProxyConfigTool: Tool {
    let name = "proxy_config"
    let description = "Check whether system HTTP/HTTPS/SOCKS proxies are enabled per network service."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Optional focus; use empty string if none")
        var note: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.proxyConfig()
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct VpnInterfacesTool: Tool {
    let name = "vpn_interfaces"
    let description = "List VPN-like interfaces and whether the current network path uses them."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Optional focus; use empty string if none")
        var note: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.vpnInterfaces()
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct HostsFileTool: Tool {
    let name = "hosts_file"
    let description = "Read /etc/hosts and highlight surprising overrides."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Optional focus; use empty string if none")
        var note: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.hostsFile()
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
struct CurrentWifiTool: Tool {
    let name = "current_wifi"
    let description = "Show current Wi-Fi association (SSID/BSSID if Location allows). Not an RSSI survey."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "Optional focus; use empty string if none")
        var note: String
    }

    func call(arguments: Arguments) async throws -> ToolOutput {
        activity.note(name)
        let report = await DiagnosticServices.shared.currentWifi()
        return ToolOutput(report.markdown)
    }
}

@available(macOS 26.0, *)
enum DiagnosticToolset {
    static func make(activity: ToolActivityHub) -> [any Tool] {
        [
            InterfacesTool(activity: activity),
            DefaultRouteTool(activity: activity),
            PathStatusTool(activity: activity),
            DnsConfigTool(activity: activity),
            DnsLookupTool(activity: activity),
            ReachabilityTool(activity: activity),
            HttpProbeTool(activity: activity),
            ProxyConfigTool(activity: activity),
            VpnInterfacesTool(activity: activity),
            HostsFileTool(activity: activity),
            CurrentWifiTool(activity: activity),
        ]
    }
}

#endif
