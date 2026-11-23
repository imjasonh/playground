import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Narrow, single-finding investigator for the Inspector drawer.
/// Unlike Onramp's 15-tool chat loop, this session starts fresh per question,
/// carries only ONE finding's compact context, and exposes at most 3 tiny read-only tools.
enum ScopedInvestigator {
    struct InvestigationAnswer: Equatable, Sendable {
        var text: String
        var usedTools: [String]
        var usedAFM: Bool
    }

    static func answer(
        question: String,
        finding: Finding,
        relatedDevice: LANDevice?
    ) async -> InvestigationAnswer {
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *), FoundationModelsAvailability.evaluate().isAvailable {
            let tracker = ToolCallTracker()
            let tools: [any Tool] = [
                ProbeHostTool(tracker: tracker),
                CheckUPnPTool(tracker: tracker),
                InspectHostProcessTool(tracker: tracker),
            ]
            let session = LanguageModelSession(
                tools: tools,
                instructions: """
                You are Lantern's focused network investigator. Answer the user's question \
                about THIS specific finding concisely (under 120 words). Use a tool only if \
                fresh live verification is needed. Never invent IPs, ports, or causes. \
                Tools are read-only; never claim you changed anything.
                """
            )
            let prompt = buildScopedPrompt(
                question: question,
                finding: finding,
                relatedDevice: relatedDevice
            )
            do {
                let response = try await session.respond(to: prompt)
                return InvestigationAnswer(
                    text: response.content.trimmingCharacters(in: .whitespacesAndNewlines),
                    usedTools: tracker.recorded(),
                    usedAFM: true
                )
            } catch {
                // Fall back gracefully if the 4k window or generation stalls.
                return InvestigationAnswer(
                    text: deterministicFallback(finding: finding, relatedDevice: relatedDevice),
                    usedTools: tracker.recorded(),
                    usedAFM: false
                )
            }
        }
        #endif
        return InvestigationAnswer(
            text: deterministicFallback(finding: finding, relatedDevice: relatedDevice),
            usedTools: [],
            usedAFM: false
        )
    }

    static func buildScopedPrompt(
        question: String,
        finding: Finding,
        relatedDevice: LANDevice?
    ) -> String {
        var lines = [
            "Finding: [\(finding.severity.rawValue)] \(finding.title)",
            "Summary: \(finding.summary)",
        ]
        if !finding.evidence.isEmpty {
            lines.append("Evidence: " + finding.evidence.prefix(4).joined(separator: "; "))
        }
        if let dev = relatedDevice {
            let ports = dev.openPorts.map { "\($0.port)/\($0.serviceName)" }.joined(separator: ", ")
            lines.append("Device: \(dev.displayName) ip=\(dev.ipAddress) mac=\(dev.macAddress) vendor=\(dev.vendor ?? "unknown") ports=[\(ports)]")
        }
        lines.append("User question: \(question)")
        return lines.joined(separator: "\n")
    }

    static func deterministicFallback(finding: Finding, relatedDevice: LANDevice?) -> String {
        let base = FindingExplainer.fallback(for: finding)
        var parts = [base.whyItMatters, "Next step: \(base.nextStep)"]
        if let dev = relatedDevice {
            parts.append("Device: \(dev.displayName) (\(dev.ipAddress), \(dev.macAddress)).")
        }
        return parts.joined(separator: "\n\n")
    }
}

#if canImport(FoundationModels)
@available(macOS 26.0, *)
private final class ToolCallTracker: @unchecked Sendable {
    private let lock = NSLock()
    private var names: [String] = []

    func record(_ name: String) {
        lock.lock()
        names.append(name)
        lock.unlock()
    }

    func recorded() -> [String] {
        lock.lock()
        defer { lock.unlock() }
        return names
    }
}

@available(macOS 26.0, *)
private struct ProbeHostTool: Tool {
    let name = "probe_host"
    let description = "Re-probe high-signal proxy/debug TCP ports on one local IP."
    let tracker: ToolCallTracker

    @Generable
    struct Arguments {
        @Guide(description: "Local IPv4 address to probe, e.g. 192.168.1.42")
        var ipAddress: String
    }

    func call(arguments: Arguments) async throws -> String {
        tracker.record(name)
        let ports = await PortProbeCollector.probeHost(ip: arguments.ipAddress)
        if ports.isEmpty {
            return "No probed ports open on \(arguments.ipAddress)."
        }
        let summary = ports.map { "\($0.port) (\($0.serviceName))" }.joined(separator: ", ")
        return "Open ports on \(arguments.ipAddress): \(summary)"
    }
}

@available(macOS 26.0, *)
private struct CheckUPnPTool: Tool {
    let name = "check_upnp"
    let description = "Re-query the router for active UPnP inbound port forwards."
    let tracker: ToolCallTracker

    @Generable
    struct Arguments {}

    func call(arguments: Arguments) async throws -> String {
        tracker.record(name)
        let mappings = await UPnPCollector.collect()
        if mappings.isEmpty {
            return "No active UPnP port mappings reported by the router."
        }
        return mappings.prefix(8).map {
            "\($0.protocolName) :\($0.externalPort) -> \($0.internalClient):\($0.internalPort) (\($0.description))"
        }.joined(separator: "\n")
    }
}

@available(macOS 26.0, *)
private struct InspectHostProcessTool: Tool {
    let name = "inspect_process"
    let description = "Check a Mac process's live external connections, fan-out, and wildcard listeners."
    let tracker: ToolCallTracker

    @Generable
    struct Arguments {
        @Guide(description: "Process name substring to inspect")
        var processName: String
    }

    func call(arguments: Arguments) async throws -> String {
        tracker.record(name)
        let query = arguments.processName.lowercased()
        let matches = HostTrafficCollector.collect().filter {
            $0.processName.lowercased().contains(query)
        }
        guard let top = matches.first else {
            return "No active network sockets found for '\(arguments.processName)'."
        }
        let listeners = top.listeningWildcardPorts.map(String.init).joined(separator: ", ")
        return "\(top.processName) (pid \(top.pid)): \(top.uniqueRemoteIPs) remote IPs across \(top.uniqueRemoteSubnets) /16 subnets, out=\(top.bytesOut)B in=\(top.bytesIn)B, wildcardListeners=[\(listeners)]"
    }
}
#endif
