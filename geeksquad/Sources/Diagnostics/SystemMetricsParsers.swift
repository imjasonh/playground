import Foundation

// MARK: - Disk space (`df -kP`)

struct DiskVolume: Equatable, Sendable {
    var filesystem: String
    var totalKilobytes: Int
    var usedKilobytes: Int
    var availableKilobytes: Int
    var capacityPercent: Int
    var mountPoint: String

    var availableGigabytes: Double { Double(availableKilobytes) / 1_048_576.0 }
    var totalGigabytes: Double { Double(totalKilobytes) / 1_048_576.0 }
}

enum DiskSpaceParser {
    static func parse(_ text: String) -> [DiskVolume] {
        var volumes: [DiskVolume] = []
        for raw in text.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            guard !line.isEmpty, !line.lowercased().hasPrefix("filesystem") else { continue }
            let parts = line.split(omittingEmptySubsequences: true, whereSeparator: \.isWhitespace)
            // filesystem blocks used avail capacity% mount (mount may have spaces — rare on macOS root)
            guard parts.count >= 6,
                  let total = Int(parts[1]),
                  let used = Int(parts[2]),
                  let avail = Int(parts[3])
            else { continue }
            let capRaw = parts[4].trimmingCharacters(in: CharacterSet(charactersIn: "%"))
            guard let cap = Int(capRaw) else { continue }
            let mount = parts[5...].joined(separator: " ")
            volumes.append(
                DiskVolume(
                    filesystem: String(parts[0]),
                    totalKilobytes: total,
                    usedKilobytes: used,
                    availableKilobytes: avail,
                    capacityPercent: cap,
                    mountPoint: mount
                )
            )
        }
        return volumes
    }

    static func summarize(_ volumes: [DiskVolume]) -> (body: String, proposedFixes: [String]) {
        let interesting = volumes.filter { volume in
            volume.mountPoint == "/"
                || volume.mountPoint.hasPrefix("/System/Volumes/Data")
                || volume.mountPoint.hasPrefix("/Volumes/")
        }
        let focus = interesting.isEmpty ? volumes : interesting
        guard !focus.isEmpty else {
            return ("No volumes parsed from df.", ["Try Disk Utility → View → Show All Devices."])
        }

        var lines: [String] = ["Mounted volumes (selected):", ""]
        var fixes: [String] = []
        for volume in focus.prefix(12) {
            lines.append(
                String(
                    format: "%@ — %.1f GB free of %.1f GB (%d%% used)",
                    volume.mountPoint,
                    volume.availableGigabytes,
                    volume.totalGigabytes,
                    volume.capacityPercent
                )
            )
            if volume.mountPoint == "/" || volume.mountPoint.hasPrefix("/System/Volumes/Data") {
                if volume.availableGigabytes < 5 || volume.capacityPercent >= 95 {
                    fixes.append(
                        "Startup disk is nearly full (\(volume.capacityPercent)% used, \(String(format: "%.1f", volume.availableGigabytes)) GB free). Free space (Large files / Downloads / Caches) or empty Trash; low free space makes Macs feel slow."
                    )
                } else if volume.availableGigabytes < 20 || volume.capacityPercent >= 90 {
                    fixes.append(
                        "Startup disk is getting tight (\(String(format: "%.1f", volume.availableGigabytes)) GB free). Free some space before it hits critically low."
                    )
                }
            }
        }
        if fixes.isEmpty {
            fixes.append("Disk free space looks OK on the volumes above. If the Mac is still slow, check memory pressure, CPU, and the heavy app with process tools.")
        }
        return (lines.joined(separator: "\n"), fixes)
    }
}

// MARK: - vm_stat

struct VmStatSummary: Equatable, Sendable {
    var pageSizeBytes: Int
    var pagesFree: Int
    var pagesActive: Int
    var pagesInactive: Int
    var pagesSpeculative: Int
    var pagesWired: Int
    var pagesCompressed: Int
    var swapins: Int
    var swapouts: Int

    var freeMegabytes: Double { Double(pagesFree * pageSizeBytes) / 1_048_576.0 }
    var wiredMegabytes: Double { Double(pagesWired * pageSizeBytes) / 1_048_576.0 }
    var compressedMegabytes: Double { Double(pagesCompressed * pageSizeBytes) / 1_048_576.0 }
}

enum VmStatParser {
    static func parse(_ text: String) -> VmStatSummary? {
        var pageSize = 4096
        if let range = text.range(of: "page size of ", options: .caseInsensitive) {
            let after = text[range.upperBound...]
            if let size = Int(after.prefix(while: \.isNumber)), size > 0 {
                pageSize = size
            }
        }

        func value(_ key: String) -> Int {
            for raw in text.split(whereSeparator: \.isNewline) {
                let line = raw.trimmingCharacters(in: .whitespaces)
                guard line.lowercased().hasPrefix(key.lowercased()) else { continue }
                let digits = line.split(separator: ":").last?
                    .trimmingCharacters(in: .whitespacesAndNewlines)
                    .replacingOccurrences(of: ".", with: "")
                    .replacingOccurrences(of: ",", with: "")
                return Int(digits ?? "") ?? 0
            }
            return 0
        }

        guard text.localizedCaseInsensitiveContains("Pages free") else { return nil }

        return VmStatSummary(
            pageSizeBytes: pageSize,
            pagesFree: value("Pages free"),
            pagesActive: value("Pages active"),
            pagesInactive: value("Pages inactive"),
            pagesSpeculative: value("Pages speculative"),
            pagesWired: value("Pages wired"),
            pagesCompressed: value("Pages occupied by compressor"),
            swapins: value("Swapins"),
            swapouts: value("Swapouts")
        )
    }

    static func summarize(_ stats: VmStatSummary, physicalMemoryBytes: UInt64) -> (body: String, proposedFixes: [String]) {
        let ramGB = Double(physicalMemoryBytes) / 1_073_741_824.0
        var lines = [
            String(format: "Physical RAM: %.1f GB", ramGB),
            String(format: "Page size: %d bytes", stats.pageSizeBytes),
            String(format: "Free: %.0f MB", stats.freeMegabytes),
            String(format: "Wired: %.0f MB", stats.wiredMegabytes),
            String(format: "Compressor: %.0f MB", stats.compressedMegabytes),
            "Swapins: \(stats.swapins)",
            "Swapouts: \(stats.swapouts)",
        ]
        var fixes: [String] = []
        if stats.swapouts > 1000 || stats.compressedMegabytes > 1024 {
            fixes.append(
                "Memory looks pressured (compressor/swap activity). Quit heavy apps and re-check; look at top_memory / process_usage for the biggest consumers. (Don’t suggest upgrading RAM — that’s not practical on most Macs.)"
            )
        } else if stats.freeMegabytes < 256 && stats.compressedMegabytes > 512 {
            fixes.append("Free RAM is low with notable compression — close unused apps and re-check.")
        } else {
            fixes.append("Memory pressure indicators look moderate from vm_stat. If the UI still feels laggy, check CPU (top_cpu) and disk free space.")
        }
        lines.append("")
        lines.append("Note: This is a snapshot from vm_stat, not Activity Monitor’s Memory Pressure graph.")
        return (lines.joined(separator: "\n"), fixes)
    }
}

// MARK: - Listening TCP ports (`lsof -nP -iTCP -sTCP:LISTEN`)

struct ListeningPort: Equatable, Sendable {
    var command: String
    var pid: Int
    var address: String
}

enum ListeningPortsParser {
    static func parse(_ text: String) -> [ListeningPort] {
        var rows: [ListeningPort] = []
        for raw in text.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            guard !line.isEmpty, !line.hasPrefix("COMMAND") else { continue }
            let parts = line.split(omittingEmptySubsequences: true, whereSeparator: \.isWhitespace)
            guard parts.count >= 9, let pid = Int(parts[1]) else { continue }
            let name = String(parts[parts.count - 2]) // e.g. *:3000 or 127.0.0.1:5432
            guard name.contains(":") else { continue }
            rows.append(ListeningPort(command: String(parts[0]), pid: pid, address: name))
        }
        // Dedupe command+address+pid
        var seen = Set<String>()
        return rows.filter { row in
            let key = "\(row.pid)|\(row.address)"
            if seen.contains(key) { return false }
            seen.insert(key)
            return true
        }
        .sorted { $0.address < $1.address }
    }

    static func summarize(_ ports: [ListeningPort], filterPort: Int?) -> (body: String, proposedFixes: [String]) {
        let filtered: [ListeningPort]
        if let filterPort {
            filtered = ports.filter { $0.address.hasSuffix(":\(filterPort)") }
        } else {
            filtered = ports
        }
        guard !filtered.isEmpty else {
            if let filterPort {
                return (
                    "No process is listening on TCP port \(filterPort).",
                    ["If an app failed to bind, something else may have exited — start the server again or pick a free port."]
                )
            }
            return ("No listening TCP ports found (unexpected).", ["Try again; lsof may need a moment after boot."])
        }

        var lines = ["Listening TCP ports\(filterPort.map { " (port \($0))" } ?? ""):", ""]
        for row in filtered.prefix(40) {
            let cmd = row.command.padding(toLength: 18, withPad: " ", startingAt: 0)
            lines.append("  \(cmd)  pid \(row.pid)  \(row.address)")
        }
        if filtered.count > 40 {
            lines.append("  …and \(filtered.count - 40) more")
        }
        var fixes: [String] = [
            "If a dev server won’t start because the port is busy, quit the listed process (Activity Monitor) or choose another port."
        ]
        if let filterPort, !filtered.isEmpty {
            fixes.insert(
                "Port \(filterPort) is in use by \(filtered.map(\.command).joined(separator: ", ")).",
                at: 0
            )
        }
        return (lines.joined(separator: "\n"), fixes)
    }
}

// MARK: - Crash reports

struct CrashReportFile: Equatable, Sendable {
    var name: String
    var path: String
    var modified: Date
}

enum CrashReportsScanner {
    static func scan(directories: [URL], query: String?, limit: Int, now: Date = Date()) -> [CrashReportFile] {
        let fm = FileManager.default
        var files: [CrashReportFile] = []
        let needle = query?.trimmingCharacters(in: .whitespacesAndNewlines).lowercased() ?? ""
        for dir in directories {
            guard let contents = try? fm.contentsOfDirectory(
                at: dir,
                includingPropertiesForKeys: [.contentModificationDateKey, .isRegularFileKey],
                options: [.skipsHiddenFiles]
            ) else { continue }
            for url in contents {
                let name = url.lastPathComponent
                let lower = name.lowercased()
                guard lower.hasSuffix(".ips") || lower.hasSuffix(".crash") || lower.hasSuffix(".diagnostic")
                else { continue }
                if !needle.isEmpty && !lower.contains(needle) { continue }
                let values = try? url.resourceValues(forKeys: [.contentModificationDateKey, .isRegularFileKey])
                guard values?.isRegularFile == true, let modified = values?.contentModificationDate else { continue }
                // Ignore ancient noise (> 60 days) unless querying a specific app.
                if needle.isEmpty, now.timeIntervalSince(modified) > 60 * 24 * 3600 { continue }
                files.append(CrashReportFile(name: name, path: url.path, modified: modified))
            }
        }
        return Array(
            files.sorted { $0.modified > $1.modified }.prefix(max(limit, 1))
        )
    }

    static func summarize(_ files: [CrashReportFile], query: String?) -> (body: String, proposedFixes: [String]) {
        let formatter = DateFormatter()
        formatter.dateStyle = .medium
        formatter.timeStyle = .short
        if files.isEmpty {
            let q = query?.trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
            if q.isEmpty {
                return (
                    "No recent crash reports found in the standard DiagnosticReports folders.",
                    ["If an app quit unexpectedly, reproduce once and re-run; reports can take a minute to appear."]
                )
            }
            return (
                "No recent crash reports matched “\(q)”.",
                ["Confirm the app name fragment, reproduce the crash, then re-check."]
            )
        }
        var lines = ["Recent crash / diagnostic reports:", ""]
        for file in files {
            lines.append("  \(formatter.string(from: file.modified))  \(file.name)")
        }
        lines.append("")
        lines.append("Paths are under ~/Library/Logs/DiagnosticReports and /Library/Logs/DiagnosticReports.")
        return (
            lines.joined(separator: "\n"),
            [
                "Open the newest report in Console (or Quick Look) to see the crashing exception.",
                "Update or reinstall the app; if it keeps crashing after an OS update, check the vendor’s release notes.",
                "Geek Squad lists reports only — it does not delete or submit them.",
            ]
        )
    }
}
