import Foundation

/// One row from `ps` (`pid`, `rss` in KiB, `%cpu`, `command`).
struct ProcessRow: Equatable, Sendable {
    var pid: Int
    var rssKilobytes: Int
    var cpuPercent: Double
    var command: String

    var rssMegabytes: Double { Double(rssKilobytes) / 1024.0 }

    var shortName: String {
        let trimmed = command.trimmingCharacters(in: .whitespacesAndNewlines)
        if trimmed.hasPrefix("/") {
            return URL(fileURLWithPath: trimmed.split(separator: " ").first.map(String.init) ?? trimmed)
                .lastPathComponent
        }
        return trimmed.split(separator: " ").first.map(String.init) ?? trimmed
    }
}

enum ProcessListParser {
    /// Parses `ps -axo pid=,rss=,%cpu=,command=` style output (macOS).
    static func parse(_ text: String) -> [ProcessRow] {
        var rows: [ProcessRow] = []
        for raw in text.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            guard !line.isEmpty else { continue }
            let parts = line.split(maxSplits: 3, omittingEmptySubsequences: true, whereSeparator: \.isWhitespace)
            guard parts.count >= 4,
                  let pid = Int(parts[0]),
                  let rss = Int(parts[1]),
                  let cpu = Double(parts[2])
            else { continue }
            let command = String(parts[3]).trimmingCharacters(in: .whitespaces)
            guard !command.isEmpty else { continue }
            rows.append(ProcessRow(pid: pid, rssKilobytes: rss, cpuPercent: cpu, command: command))
        }
        return rows
    }

    /// Case-insensitive match on command line or basename (e.g. "Cursor" → Cursor + helpers).
    static func matching(_ rows: [ProcessRow], query: String) -> [ProcessRow] {
        let q = query.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !q.isEmpty else { return [] }
        let needle = q.lowercased()
        return rows.filter { row in
            row.command.lowercased().contains(needle) || row.shortName.lowercased().contains(needle)
        }
    }

    static func summarize(
        matches: [ProcessRow],
        query: String,
        physicalMemoryBytes: UInt64
    ) -> (body: String, proposedFixes: [String]) {
        guard !matches.isEmpty else {
            return (
                "No running processes matched “\(query)”. Check the name (Activity Monitor → process name) or that the app is open.",
                ["Launch the app and re-run this check.", "Try a shorter name fragment (e.g. Cursor, Chrome, Slack)."]
            )
        }

        let sorted = matches.sorted { $0.rssKilobytes > $1.rssKilobytes }
        let totalRSS = sorted.reduce(0) { $0 + $1.rssKilobytes }
        let totalMB = Double(totalRSS) / 1024.0
        let peakCPU = sorted.map(\.cpuPercent).max() ?? 0
        let ramGB = Double(physicalMemoryBytes) / 1_073_741_824.0
        let pctOfRAM = physicalMemoryBytes > 0
            ? (Double(totalRSS) * 1024.0 / Double(physicalMemoryBytes)) * 100.0
            : 0

        var lines: [String] = []
        lines.append("Query: \(query)")
        lines.append("Matching processes: \(sorted.count)")
        lines.append(String(format: "Total memory (RSS): %.0f MB (%.1f%% of %.1f GB RAM)", totalMB, pctOfRAM, ramGB))
        lines.append(String(format: "Peak CPU among matches: %.1f%%", peakCPU))
        lines.append("")
        lines.append("Top by memory:")
        for row in sorted.prefix(12) {
            lines.append(
                String(
                    format: "  pid %-6d  %7.0f MB  %5.1f%% CPU  %@",
                    row.pid,
                    row.rssMegabytes,
                    row.cpuPercent,
                    row.shortName
                )
            )
        }
        if sorted.count > 12 {
            lines.append("  …and \(sorted.count - 12) more")
        }

        var fixes: [String] = []
        if pctOfRAM >= 15 || totalMB >= 2048 {
            fixes.append(
                String(
                    format: "“%@” is using a large share of RAM (%.0f MB). Quit and relaunch the app, or close heavy windows/tabs; if it climbs again, check for an update or report a memory leak to the app’s support.",
                    query,
                    totalMB
                )
            )
        } else if pctOfRAM >= 8 || totalMB >= 1024 {
            fixes.append(
                String(
                    format: "Memory use is elevated but not extreme (%.0f MB). If the Mac feels slow, quit other heavy apps or relaunch “%@”.",
                    totalMB,
                    query
                )
            )
        } else {
            fixes.append(
                String(
                    format: "Memory use for “%@” looks moderate (%.0f MB). If it’s still slow, check CPU in a moment, disk/network waits, or that app’s own diagnostics — Geek Squad can re-check after you reproduce the slowness.",
                    query,
                    totalMB
                )
            )
        }
        if peakCPU >= 80 {
            fixes.append(
                String(
                    format: "CPU is high (%.0f%% on at least one related process). Wait for the work to finish, or force-quit from Activity Monitor if it’s stuck.",
                    peakCPU
                )
            )
        }
        if matches.contains(where: Self.isSpotlightRelated) {
            fixes.append(
                "Spotlight / metadata processes (mds, mdworker) are in this set. If they’re hot after a big copy or OS update, wait for indexing to finish, or check System Settings → Siri & Spotlight. Rebuilding the index is a last resort."
            )
        }
        fixes.append("Geek Squad only reports usage — it does not quit or kill processes for you.")
        return (lines.joined(separator: "\n"), fixes)
    }

    static func isSpotlightRelated(_ row: ProcessRow) -> Bool {
        let name = row.shortName.lowercased()
        let command = row.command.lowercased()
        return name.contains("mds")
            || name.contains("mdworker")
            || name.contains("spotlight")
            || command.contains("/mds")
            || command.contains("mdworker")
    }
}
