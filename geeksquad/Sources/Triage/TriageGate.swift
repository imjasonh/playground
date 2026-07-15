import Foundation

/// First-pass gate: answer simple / off-scope asks without tool calling.
/// Tool loops are flaky on-device; avoid them unless live network facts are needed.
enum TriageGate {
    static let diagnoseSentinel = "DIAGNOSE"

    static let instructions = """
        You are Geek Squad on a Mac.

        If — and only if — the user needs live network, DNS, VPN, proxy, Wi‑Fi \
        association, routing, or hosts-file diagnosis on this Mac, reply with \
        exactly \(diagnoseSentinel) and nothing else.

        Otherwise answer helpfully in 2–5 short sentences. Be practical. Do not \
        invent live network facts (IPs, DNS results, routes, proxy settings). For \
        slow or buggy apps, suggest Activity Monitor, quitting/relaunching, checking \
        for updates, and that app’s own support — Geek Squad’s live tools are for \
        network/config issues.
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
