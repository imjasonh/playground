import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Shared triage system prompt for the on-device model (tool-using path).
enum TriageInstructions {
    static let text = """
        You are Geek Squad, an offline Mac technician for network/config and \
        local process resource checks.
        The user describes what they see and what they want fixed.

        Scope:
        - Network and configuration (connectivity, DNS, VPN, proxy, Wi‑Fi, \
        routing, hosts file).
        - App/process CPU and memory on this Mac (process_usage, top_memory).
        - If the question is outside those areas, say so briefly and suggest a \
        next step — do not invent live measurements.

        Rules:
        - Use diagnostic tools to gather facts before concluding. For slow apps \
        or “is it using too much memory/CPU?”, call process_usage with the app \
        name (e.g. Cursor). For “what’s using my memory?”, call top_memory.
        - For network issues prefer path_status, default_route, dns_config, and \
        interfaces early; then dig deeper as needed. Call only what you need — \
        usually 2–4 tools.
        - Never invent IP addresses, DNS results, routes, proxy settings, or \
        CPU/memory numbers — only cite tool output.
        - Do not invent what an app is (e.g. do not call Cursor a note-taking app).
        - Propose clear, numbered steps the user can take themselves. Do not claim \
        you changed System Settings, killed processes, ran sudo, or applied a fix.
        - Be concise and practical. Lead with the likely cause, then evidence, then \
        proposed fixes.
        - If a tool fails or returns empty, say so and try another angle.
        """
}

#if canImport(FoundationModels)

/// Notifies the UI when a diagnostic tool runs and keeps compact reports for
/// fallback if generation fails after tools succeed.
@available(macOS 26.0, *)
final class ToolActivityHub: @unchecked Sendable {
    private let handler: @Sendable (String) -> Void
    private let lock = NSLock()
    private var reports: [(name: String, markdown: String)] = []

    init(handler: @escaping @Sendable (String) -> Void) {
        self.handler = handler
    }

    func note(_ name: String) {
        handler(name)
    }

    func record(name: String, report: DiagnosticReport) {
        let compact = report.compactMarkdown()
        lock.lock()
        reports.append((name, compact))
        if reports.count > 8 {
            reports.removeFirst(reports.count - 8)
        }
        lock.unlock()
    }

    func clearReports() {
        lock.lock()
        reports.removeAll()
        lock.unlock()
    }

    /// Markdown the UI can show if the model stalls after tools ran.
    func fallbackMarkdown() -> String? {
        lock.lock()
        let snapshot = reports
        lock.unlock()
        guard !snapshot.isEmpty else { return nil }
        return snapshot.map { "### \($0.name)\n\n\($0.markdown)" }.joined(separator: "\n\n")
    }
}

@available(macOS 26.0, *)
private func runTool(
    _ name: String,
    activity: ToolActivityHub,
    _ work: () async -> DiagnosticReport
) async -> String {
    activity.note(name)
    let report = await work()
    activity.record(name: name, report: report)
    return report.compactMarkdown()
}

@available(macOS 26.0, *)
struct InterfacesTool: Tool {
    let name = "interfaces"
    let description = "List network interfaces with addresses; note VPN-like utun/ipsec/ppp interfaces."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.interfaces()
        }
    }
}

@available(macOS 26.0, *)
struct DefaultRouteTool: Tool {
    let name = "default_route"
    let description = "Show the Mac's default route (gateway and interface), including whether traffic exits via VPN."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.defaultRoute()
        }
    }
}

@available(macOS 26.0, *)
struct PathStatusTool: Tool {
    let name = "path_status"
    let description = "Snapshot of NWPathMonitor: satisfied/unsatisfied, expensive, constrained, interfaces, IP/DNS support."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.pathStatus()
        }
    }
}

@available(macOS 26.0, *)
struct DnsConfigTool: Tool {
    let name = "dns_config"
    let description = "Summarize configured DNS resolvers and search domains (from scutil --dns)."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.dnsConfig()
        }
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

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.dnsLookup(hostname: arguments.hostname)
        }
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

    func call(arguments: Arguments) async throws -> String {
        let port = UInt16(clamping: arguments.port)
        return await runTool(name, activity: activity) {
            await DiagnosticServices.shared.reachability(host: arguments.host, port: port)
        }
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

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.httpProbe(urlString: arguments.url)
        }
    }
}

@available(macOS 26.0, *)
struct ProxyConfigTool: Tool {
    let name = "proxy_config"
    let description = "Check whether system HTTP/HTTPS/SOCKS proxies are enabled per network service."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.proxyConfig()
        }
    }
}

@available(macOS 26.0, *)
struct VpnInterfacesTool: Tool {
    let name = "vpn_interfaces"
    let description = "List VPN-like interfaces and whether the current network path uses them."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.vpnInterfaces()
        }
    }
}

@available(macOS 26.0, *)
struct HostsFileTool: Tool {
    let name = "hosts_file"
    let description = "Read /etc/hosts and highlight surprising overrides."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.hostsFile()
        }
    }
}

@available(macOS 26.0, *)
struct CurrentWifiTool: Tool {
    let name = "current_wifi"
    let description = "Show current Wi-Fi association (SSID/BSSID if Location allows). Not an RSSI survey."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.currentWifi()
        }
    }
}

@available(macOS 26.0, *)
struct ProcessUsageTool: Tool {
    let name = "process_usage"
    let description = "Measure live CPU and memory (RSS) for processes matching an app or process name on this Mac."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "App or process name fragment, e.g. Cursor, Safari, Chrome")
        var query: String
    }

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.processUsage(query: arguments.query)
        }
    }
}

@available(macOS 26.0, *)
struct TopMemoryTool: Tool {
    let name = "top_memory"
    let description = "List the processes using the most memory (RSS) on this Mac right now."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.topMemoryProcesses()
        }
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
            ProcessUsageTool(activity: activity),
            TopMemoryTool(activity: activity),
        ]
    }
}

#endif
