import Foundation

/// Host sanitization + light parsers for ICMP/path CLI output (read-only probes).
enum NetworkProbeHost {
    /// Accepts a hostname/IP, or strips `https://…` / path junk users paste in.
    static func sanitize(_ raw: String) -> String? {
        var host = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !host.isEmpty else { return nil }

        if let url = URL(string: host),
           let extracted = url.host,
           url.scheme == "http" || url.scheme == "https"
        {
            host = extracted
        } else if let slash = host.firstIndex(of: "/") {
            host = String(host[..<slash])
        }

        host = host.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !host.isEmpty, host.count <= 253 else { return nil }

        let allowed = CharacterSet.alphanumerics.union(CharacterSet(charactersIn: ".-:%_"))
        guard host.unicodeScalars.allSatisfy({ allowed.contains($0) }) else { return nil }
        return host
    }
}

enum PingOutputParser {
    struct Summary: Equatable {
        var transmitted: Int?
        var received: Int?
        var lossPercent: Double?
        var roundTripAvgMs: Double?
    }

    static func summarize(_ text: String) -> Summary {
        var summary = Summary()
        // macOS: "4 packets transmitted, 4 packets received, 0.0% packet loss"
        // Linux-ish: "4 packets transmitted, 4 received, 0% packet loss"
        if let match = firstMatch(
            in: text,
            pattern: #"(\d+)\s+packets transmitted,\s+(\d+)\s+(?:packets )?received,\s+([0-9.]+)%\s+packet loss"#
        ) {
            summary.transmitted = Int(match[0])
            summary.received = Int(match[1])
            summary.lossPercent = Double(match[2])
        }
        // macOS: "round-trip min/avg/max/stddev = 12.1/15.2/20.3/3.1 ms"
        if let match = firstMatch(
            in: text,
            pattern: #"round-trip [^=]*=\s*[0-9.]+/([0-9.]+)/[0-9.]+/[0-9.]+\s+ms"#
        ) {
            summary.roundTripAvgMs = Double(match[0])
        }
        return summary
    }

    static func proposedFixes(for summary: Summary, host: String) -> [String] {
        var fixes: [String] = []
        if let loss = summary.lossPercent, loss >= 25 {
            fixes.append(
                "High packet loss to \(host) (\(Int(loss))%). Try another network, disconnect VPN, or check Wi‑Fi signal under System Settings → Network."
            )
        } else if let received = summary.received, received == 0 {
            fixes.append(
                "No ICMP replies from \(host). Many networks block ping — try reachability (TCP 443) or http_probe next."
            )
        } else if let avg = summary.roundTripAvgMs, avg >= 200 {
            fixes.append(
                "Latency to \(host) looks high (~\(Int(avg)) ms avg). Check VPN/Wi‑Fi, or run traceroute to see where delay starts."
            )
        }
        return fixes
    }

    private static func firstMatch(in text: String, pattern: String) -> [String]? {
        guard let regex = try? NSRegularExpression(pattern: pattern, options: [.caseInsensitive]) else {
            return nil
        }
        let range = NSRange(text.startIndex..<text.endIndex, in: text)
        guard let match = regex.firstMatch(in: text, options: [], range: range), match.numberOfRanges > 1 else {
            return nil
        }
        var parts: [String] = []
        for i in 1..<match.numberOfRanges {
            guard let r = Range(match.range(at: i), in: text) else { return nil }
            parts.append(String(text[r]))
        }
        return parts
    }
}

enum TracerouteOutputParser {
    static func proposedFixes(text: String, host: String, timedOut: Bool) -> [String] {
        var fixes: [String] = []
        let stars = text.split(whereSeparator: \.isNewline).filter { $0.contains("* * *") }.count
        if timedOut {
            fixes.append(
                "Traceroute to \(host) ran long or stalled. Partial hops above still help — compare early vs late timeouts."
            )
        }
        if stars >= 3 {
            fixes.append(
                "Several hops timed out (`* * *`). That can be normal (ICMP filtered) — combine with ping and reachability before blaming the path."
            )
        }
        if text.localizedCaseInsensitiveContains("utun") || text.localizedCaseInsensitiveContains("vpn") {
            fixes.append(
                "Path may involve a VPN tunnel. Disconnect VPN under System Settings → Network and re-check."
            )
        }
        return fixes
    }
}
