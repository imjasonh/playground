import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Shared triage system prompt for the on-device model (tool-using path).
enum TriageInstructions {
    static let text = """
        You are Geek Squad, an offline Mac technician. You diagnose network/config, \
        performance, and common local functionality issues with live tools.
        The user describes what they see and what they want fixed.

        \(TriageAudience.guidance)

        Scope (use tools — never invent measurements):
        - Network/config: path_status, default_route, dns_config, interfaces, \
        dns_lookup, reachability, http_probe, proxy_config, vpn_interfaces, \
        hosts_file, current_wifi
        - Performance: process_usage, top_memory, top_cpu, disk_space, \
        memory_pressure, system_load, power_assertions, login_items, \
        user_storage_hotspots, battery_power
        - Functionality: listening_ports (port conflicts), recent_crash_reports
        - Outside that, say so briefly — do not invent live facts or what an app “is”.

        Rules:
        - Gather facts with tools BEFORE writing the triage report. Call only what you \
        need, but for “DNS vs routing vs proxy/VPN vs hosts” style questions you MUST \
        call several of: path_status, default_route, dns_config, interfaces, \
        proxy_config, vpn_interfaces, hosts_file — plus reachability/dns_lookup/\
        http_probe as needed. Do not stop after one or two tools if the question \
        asks to separate those causes.
        - Never tell the user to inspect resolv.conf, ifconfig, dig, or other CLI \
        diagnostics themselves — that is what your tools are for.
        - Slow Mac / fans / beachball: start with system_load, disk_space, \
        memory_pressure, top_cpu (and process_usage if a named app). Add \
        login_items or user_storage_hotspots when login slowness or full disk is suspected. \
        Add battery_power when on a laptop / “slow on battery” is mentioned.
        - If mds/mdworker dominate CPU, explain Spotlight indexing — don’t tell the user \
        to force-quit indexing repeatedly.
        - Slow or heavy named app: process_usage with that name.
        - “What’s using memory/CPU?”: top_memory / top_cpu.
        - Won’t sleep / fans always on: power_assertions.
        - Port already in use / server won’t bind: listening_ports (pass the port).
        - App keeps crashing: recent_crash_reports with the app name.
        - Never invent IPs, DNS, routes, CPU%, memory MB, disk free space, or ports.
        - Your final answer is a structured triage report: headline, likelyCause, \
        evidence[], proposedSteps[]. Evidence must cite tool findings by name. \
        proposedSteps are Settings/UI actions for the user (your tools are \
        read-only). Leave proposedSteps empty when nothing needs doing — do not \
        invent filler such as “No action required.” Never list Terminal \
        diagnostic commands as steps.
        - Be concise.
        """
}

#if canImport(FoundationModels)

/// Notifies the UI when a diagnostic tool runs and keeps compact reports for
/// fallback if generation fails after tools succeed.
@available(macOS 26.0, *)
final class ToolActivityHub: @unchecked Sendable {
    /// Called with tool name + compact markdown when a tool finishes.
    private let handler: @Sendable (String, String) -> Void
    private let lock = NSLock()
    private var reports: [(name: String, markdown: String)] = []

    init(handler: @escaping @Sendable (String, String) -> Void) {
        self.handler = handler
    }

    func record(name: String, report: DiagnosticReport) {
        let compact = report.compactMarkdown()
        lock.lock()
        reports.append((name, compact))
        if reports.count > 8 {
            reports.removeFirst(reports.count - 8)
        }
        lock.unlock()
        handler(name, compact)
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
struct TopCPUTool: Tool {
    let name = "top_cpu"
    let description = "List the processes using the most CPU on this Mac right now."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.topCPUProcesses()
        }
    }
}

@available(macOS 26.0, *)
struct DiskSpaceTool: Tool {
    let name = "disk_space"
    let description = "Show free disk space on the startup disk and mounted volumes."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.diskSpace()
        }
    }
}

@available(macOS 26.0, *)
struct MemoryPressureTool: Tool {
    let name = "memory_pressure"
    let description = "Snapshot memory pressure indicators from vm_stat (free/wired/compressor/swap)."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.memoryPressure()
        }
    }
}

@available(macOS 26.0, *)
struct SystemLoadTool: Tool {
    let name = "system_load"
    let description = "Show load average, CPU count, and host uptime."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.systemLoad()
        }
    }
}

@available(macOS 26.0, *)
struct PowerAssertionsTool: Tool {
    let name = "power_assertions"
    let description = "Show power assertions that may prevent sleep or keep fans busy (pmset)."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.powerAssertions()
        }
    }
}

@available(macOS 26.0, *)
struct ListeningPortsTool: Tool {
    let name = "listening_ports"
    let description = "List processes listening on TCP ports; optional filter to one port (e.g. 3000)."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "TCP port to filter, or 0 for all listening ports")
        var port: Int
    }

    func call(arguments: Arguments) async throws -> String {
        let filter: Int? = arguments.port > 0 ? arguments.port : nil
        return await runTool(name, activity: activity) {
            await DiagnosticServices.shared.listeningPorts(port: filter)
        }
    }
}

@available(macOS 26.0, *)
struct RecentCrashReportsTool: Tool {
    let name = "recent_crash_reports"
    let description = "List recent crash/diagnostic reports, optionally filtered by app name."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {
        @Guide(description: "App name fragment to match, or empty string for any recent reports")
        var query: String
    }

    func call(arguments: Arguments) async throws -> String {
        let q = arguments.query.trimmingCharacters(in: .whitespacesAndNewlines)
        return await runTool(name, activity: activity) {
            await DiagnosticServices.shared.recentCrashReports(query: q.isEmpty ? nil : q)
        }
    }
}

@available(macOS 26.0, *)
struct LoginItemsTool: Tool {
    let name = "login_items"
    let description = "List LaunchAgents/LaunchDaemons plists that often slow login or background CPU."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.loginItems()
        }
    }
}

@available(macOS 26.0, *)
struct UserStorageHotspotsTool: Tool {
    let name = "user_storage_hotspots"
    let description = "Estimate sizes of Downloads, Caches, and other common user folders that fill the disk."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.userStorageHotspots()
        }
    }
}

@available(macOS 26.0, *)
struct BatteryPowerTool: Tool {
    let name = "battery_power"
    let description = "Show AC vs battery power source and charge percent (pmset)."
    let activity: ToolActivityHub

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        await runTool(name, activity: activity) {
            await DiagnosticServices.shared.batteryPower()
        }
    }
}

@available(macOS 26.0, *)
enum DiagnosticToolset {
    static func make(activity: ToolActivityHub, focus: TriageHeuristics.Focus?) -> [any Tool] {
        switch focus {
        case .performance:
            return performanceTools(activity: activity)
        case .network:
            return networkTools(activity: activity)
        case .functionality:
            return functionalityTools(activity: activity)
        case .general, .none:
            // Curated mixed set — not every tool — to leave room in the 4k context.
            return generalTools(activity: activity)
        }
    }

    private static func networkTools(activity: ToolActivityHub) -> [any Tool] {
        [
            PathStatusTool(activity: activity),
            DefaultRouteTool(activity: activity),
            DnsConfigTool(activity: activity),
            InterfacesTool(activity: activity),
            DnsLookupTool(activity: activity),
            ReachabilityTool(activity: activity),
            HttpProbeTool(activity: activity),
            ProxyConfigTool(activity: activity),
            VpnInterfacesTool(activity: activity),
            HostsFileTool(activity: activity),
            CurrentWifiTool(activity: activity),
        ]
    }

    private static func performanceTools(activity: ToolActivityHub) -> [any Tool] {
        [
            ProcessUsageTool(activity: activity),
            TopMemoryTool(activity: activity),
            TopCPUTool(activity: activity),
            DiskSpaceTool(activity: activity),
            MemoryPressureTool(activity: activity),
            SystemLoadTool(activity: activity),
            PowerAssertionsTool(activity: activity),
            LoginItemsTool(activity: activity),
            UserStorageHotspotsTool(activity: activity),
            BatteryPowerTool(activity: activity),
        ]
    }

    private static func functionalityTools(activity: ToolActivityHub) -> [any Tool] {
        [
            ListeningPortsTool(activity: activity),
            RecentCrashReportsTool(activity: activity),
            ProcessUsageTool(activity: activity),
            DiskSpaceTool(activity: activity),
            LoginItemsTool(activity: activity),
            PathStatusTool(activity: activity),
        ]
    }

    private static func generalTools(activity: ToolActivityHub) -> [any Tool] {
        [
            PathStatusTool(activity: activity),
            DefaultRouteTool(activity: activity),
            DnsConfigTool(activity: activity),
            ProcessUsageTool(activity: activity),
            TopCPUTool(activity: activity),
            TopMemoryTool(activity: activity),
            DiskSpaceTool(activity: activity),
            MemoryPressureTool(activity: activity),
            SystemLoadTool(activity: activity),
            ListeningPortsTool(activity: activity),
            RecentCrashReportsTool(activity: activity),
            LoginItemsTool(activity: activity),
            UserStorageHotspotsTool(activity: activity),
            BatteryPowerTool(activity: activity),
        ]
    }
}

#endif
