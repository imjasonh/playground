import Foundation

/// First-pass gate: answer without tools only when live Mac facts aren’t needed.
/// Prefer DIAGNOSE whenever process CPU/memory or network/config can be measured.
enum TriageGate {
    static let diagnoseSentinel = "DIAGNOSE"

    static let instructions = """
        You are Geek Squad on a Mac with live diagnostic tools for network/config \
        and process CPU/memory.

        Reply with exactly \(diagnoseSentinel) and nothing else when the user needs \
        live facts from this Mac, including:
        - network, DNS, VPN, proxy, Wi‑Fi association, routing, or hosts file
        - whether an app is using a lot of CPU or memory, what’s using RAM, or a \
        slow/heavy app that should be measured

        Otherwise answer helpfully in 2–5 short sentences. Be practical. Do not \
        invent measurements (memory MB, CPU %, IPs, DNS, routes). Do not invent \
        what an unfamiliar app is for — if unsure, say you’re not sure, or reply \
        \(diagnoseSentinel) so tools can measure it.
        """

    /// `nil` means run the diagnostic (tool-using) session.
    static func directAnswer(from raw: String) -> String? {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return nil }
        if needsDiagnostics(trimmed) { return nil }
        return trimmed
    }

    static func needsDiagnostics(_ raw: String) -> Bool {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        let firstLine = trimmed.split(whereSeparator: \.isNewline).first.map(String.init) ?? trimmed
        let head = firstLine.trimmingCharacters(in: .whitespacesAndNewlines).uppercased()
        return head == diagnoseSentinel || head.hasPrefix("\(diagnoseSentinel) ")
    }
}

/// Deterministic routing so “is Cursor using too much memory?” always hits tools
/// even if the on-device gate model answers with Activity Monitor homework.
enum TriageHeuristics {
    static func needsLiveDiagnostics(_ text: String) -> Bool {
        let t = text.lowercased()
        let processSignals = [
            "memory", "ram", "cpu", "process", "rss", "footprint",
            "using too much", "how much memory", "memory usage", "cpu usage",
            "activity monitor", "leak", "high memory", "eating",
        ]
        if processSignals.contains(where: { t.contains($0) }) { return true }

        let networkSignals = [
            "dns", "wifi", "wi-fi", "wi‑fi", "vpn", "proxy", "website",
            "network", "captive", "hosts file", "can't load", "cannot load",
            "routing", "default route",
        ]
        if networkSignals.contains(where: { t.contains($0) }) { return true }

        // “Cursor app is slow” / “Safari is slow” — measure before advising.
        if t.contains("slow") {
            return true
        }
        return false
    }
}
