import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Zero-tool, single-shot alert explainer (<600 tokens).
/// Translates one deterministic `Finding` into a concise, plain-English menu-bar card.
enum FindingExplainer {
    #if canImport(FoundationModels)
    @available(macOS 26.0, *)
    @Generable
    struct GeneratedExplanation {
        @Guide(description: "Crisp 5–10 word headline for a menu-bar alert")
        var headline: String

        @Guide(description: "1–2 plain-English sentences explaining why this matters on a home network")
        var whyItMatters: String

        @Guide(description: "One concrete next step the user can take (never invent terminal commands)")
        var nextStep: String
    }
    #endif

    /// Compact input prompt for AFM (unit-tested to stay well under 1k characters).
    static func makePrompt(for finding: Finding) -> String {
        var lines = [
            "Explain this home-network alert briefly for a technical homeowner.",
            "Kind: \(finding.kind.rawValue)",
            "Severity: \(finding.severity.rawValue)",
            "Title: \(finding.title)",
            "Summary: \(finding.summary)",
        ]
        if !finding.evidence.isEmpty {
            lines.append("Evidence:")
            for item in finding.evidence.prefix(5) {
                lines.append("- \(item)")
            }
        }
        return lines.joined(separator: "\n")
    }

    static func explain(_ finding: Finding) async -> FindingExplanation {
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *), FoundationModelsAvailability.evaluate().isAvailable {
            let session = LanguageModelSession(
                instructions: """
                You are Lantern, a calm home-network security monitor. \
                Explain the given alert in plain English using ONLY the provided facts. \
                Never exaggerate or invent IPs, ports, or causes.
                """
            )
            if let response = try? await session.respond(
                to: makePrompt(for: finding),
                generating: GeneratedExplanation.self
            ) {
                let content = response.content
                let headline = content.headline.trimmingCharacters(in: .whitespacesAndNewlines)
                let why = content.whyItMatters.trimmingCharacters(in: .whitespacesAndNewlines)
                let step = content.nextStep.trimmingCharacters(in: .whitespacesAndNewlines)
                if !headline.isEmpty && !why.isEmpty {
                    return FindingExplanation(
                        headline: headline,
                        whyItMatters: why,
                        nextStep: step.isEmpty ? fallback(for: finding).nextStep : step,
                        generatedByAFM: true
                    )
                }
            }
        }
        #endif
        return fallback(for: finding)
    }

    static func fallback(for finding: Finding) -> FindingExplanation {
        let nextStep: String
        switch finding.kind {
        case .newDevice:
            nextStep = "Check if you recognize this device; click Trust if it's yours, or block its MAC in your router."
        case .gatewayMACChanged:
            nextStep = "Confirm whether you replaced your router; if not, disconnect and check for ARP spoofing."
        case .deviceIPChanged:
            nextStep = "Normal after a router reboot or DHCP lease renewal; mute if expected."
        case .suspiciousOpenPort:
            nextStep = "Verify why this device exposes a proxy/debug port; disable ADB/Telnet/proxy or isolate it on a guest VLAN."
        case .newUPnPForward:
            nextStep = "Review active UPnP forwards on your router and disable UPnP if you don't need automatic port forwarding."
        case .hostProcessHighFanOut:
            nextStep = "Verify this app is expected to talk to many external IPs (e.g. P2P/VPN); uninstall if unrecognized."
        case .hostProcessWildcardListener:
            nextStep = "Confirm you intend to expose this service to the whole LAN, or mute this listener if expected."
        case .dnsConfigChanged:
            nextStep = "Check System Settings → Network → DNS to make sure your resolvers match your router or chosen DNS provider."
        case .proxyConfigChanged:
            nextStep = "Check System Settings → Network → Proxies to confirm this proxy was configured intentionally."
        case .suspiciousHostsEntry:
            nextStep = "Review /etc/hosts to confirm custom overrides are intentional."
        case .connectivityDegraded:
            nextStep = "Open Connectivity in Lantern to check DNS, VPN split-tunnel, proxy, or captive portal status."
        case .externalChattyClient:
            nextStep = "Inspect this device's DNS query log in Pi-hole / AdGuard Home to see what domain it is hammering."
        case .externalProxyDomain:
            nextStep = "A device on your LAN queried a known residential-proxy broker domain; identify and disconnect it."
        }

        return FindingExplanation(
            headline: finding.title,
            whyItMatters: finding.summary,
            nextStep: nextStep,
            generatedByAFM: false
        )
    }
}
