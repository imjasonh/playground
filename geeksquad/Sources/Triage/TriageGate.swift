import Foundation

/// First-pass gate: answer without tools only when live Mac facts aren’t needed.
enum TriageGate {
    static let diagnoseSentinel = "DIAGNOSE"

    static let instructions = """
        You are Geek Squad on a Mac with live diagnostic tools for network/config, \
        performance (CPU/memory/disk/load/sleep assertions), listening ports, and \
        crash reports.

        \(TriageAudience.guidance)

        Reply with exactly \(diagnoseSentinel) and nothing else when the user needs \
        live facts from this Mac in those areas.

        Otherwise answer helpfully in 2–5 short sentences. Be practical. Do not \
        invent measurements. Do not invent what an unfamiliar app is for — if unsure, \
        say so or reply \(diagnoseSentinel).
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

/// Deterministic routing + tool-set focus (keeps Foundation Models context smaller).
enum TriageHeuristics {
    enum Focus: String, Equatable {
        case network
        case performance
        case functionality
        case general
    }

    static func needsLiveDiagnostics(_ text: String) -> Bool {
        focus(for: text) != nil || text.lowercased().contains("slow")
    }

    /// `nil` = no strong signal (gate may still DIAGNOSE).
    static func focus(for text: String) -> Focus? {
        let t = text.lowercased()

        let functionality = [
            "port ", "port:", "listening", "bind", "already in use", "eaddrinuse",
            "crash", "crashed", "quit unexpectedly", "diagnostic report",
        ]
        if functionality.contains(where: { t.contains($0) })
            || t.contains("port") && (t.contains("in use") || t.contains("busy") || t.contains("taken"))
        {
            return .functionality
        }

        let performance = [
            "memory", "ram", "cpu", "process", "rss", "footprint",
            "using too much", "how much memory", "memory usage", "cpu usage",
            "activity monitor", "leak", "high memory", "eating",
            "disk", "storage", "free space", "fan", "therm", "won't sleep",
            "will not sleep", "cant sleep", "can't sleep", "beachball", "swap",
            "load average", "uptime", "login item", "login items", "launch agent",
            "launchagent", "caches", "downloads folder", "slow to log in", "slow login",
            "battery", "on battery", "low power", "plugged in", "charging",
            "spotlight", "indexing", "mdworker",
        ]
        if performance.contains(where: { t.contains($0) }) || t.contains("slow") {
            return .performance
        }

        let network = [
            "dns", "wifi", "wi-fi", "wi‑fi", "vpn", "proxy", "website",
            "network", "captive", "hosts file", "can't load", "cannot load",
            "routing", "default route", "offline", "connected but",
        ]
        if network.contains(where: { t.contains($0) }) {
            return .network
        }

        return nil
    }
}
