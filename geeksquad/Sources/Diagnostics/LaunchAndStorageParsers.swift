import Foundation

struct LaunchAgentItem: Equatable, Sendable {
    var label: String
    var path: String
    var scope: String // user / local / system
}

enum LaunchAgentsParser {
    /// Best-effort labels from LaunchAgents/LaunchDaemons plists (read-only).
    static func scan(directories: [(url: URL, scope: String)]) -> [LaunchAgentItem] {
        let fm = FileManager.default
        var items: [LaunchAgentItem] = []
        for entry in directories {
            guard let files = try? fm.contentsOfDirectory(
                at: entry.url,
                includingPropertiesForKeys: nil,
                options: [.skipsHiddenFiles]
            ) else { continue }
            for url in files where url.pathExtension == "plist" {
                let label = labelFromPlist(at: url) ?? url.deletingPathExtension().lastPathComponent
                items.append(LaunchAgentItem(label: label, path: url.path, scope: entry.scope))
            }
        }
        return items.sorted { $0.label.localizedCaseInsensitiveCompare($1.label) == .orderedAscending }
    }

    static func labelFromPlist(at url: URL) -> String? {
        guard let dict = NSDictionary(contentsOf: url) as? [String: Any] else { return nil }
        return dict["Label"] as? String
    }

    static func summarize(_ items: [LaunchAgentItem]) -> (body: String, proposedFixes: [String]) {
        let user = items.filter { $0.scope == "user" }
        let local = items.filter { $0.scope == "local" }
        let system = items.filter { $0.scope == "system" }
        var lines: [String] = [
            "LaunchAgents / LaunchDaemons (plist scan — not the full Login Items UI):",
            "User LaunchAgents: \(user.count)",
            "Computer LaunchAgents: \(local.count)",
            "Computer LaunchDaemons: \(system.count)",
            "",
        ]
        func appendSection(title: String, rows: [LaunchAgentItem]) {
            guard !rows.isEmpty else { return }
            lines.append(title)
            for item in rows.prefix(25) {
                lines.append("  • \(item.label)")
            }
            if rows.count > 25 {
                lines.append("  …and \(rows.count - 25) more")
            }
            lines.append("")
        }
        appendSection(title: "User (~Library/LaunchAgents):", rows: user)
        appendSection(title: "Local (/Library/LaunchAgents):", rows: local)
        appendSection(title: "Daemons (/Library/LaunchDaemons):", rows: system)

        var fixes: [String] = []
        if user.count + local.count >= 25 {
            fixes.append(
                "Many launch agents are installed (\(user.count + local.count)). Review System Settings → General → Login Items & Extensions and remove ones you don’t recognize — leftover updaters often slow login and background CPU."
            )
        } else if user.count + local.count >= 12 {
            fixes.append(
                "A moderate number of launch agents are present. If the Mac is slow after login, prune unused Login Items / background items."
            )
        } else {
            fixes.append("Launch agent count looks moderate from this scan. Also check System Settings → General → Login Items & Extensions for App background items not installed as plists.")
        }
        fixes.append("Geek Squad only lists plists — it does not unload or delete them.")
        return (lines.joined(separator: "\n"), fixes)
    }
}

struct FolderSizeSample: Equatable, Sendable {
    var name: String
    var path: String
    var kilobytes: Int?
    var error: String?

    var gigabytes: Double? {
        guard let kilobytes else { return nil }
        return Double(kilobytes) / 1_048_576.0
    }
}

enum FolderSizeParser {
    /// Parses `du -sk <path>` stdout (`12345\t/path`).
    static func parseDuSK(_ text: String) -> Int? {
        let trimmed = text.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let first = trimmed.split(whereSeparator: \.isWhitespace).first,
              let kb = Int(first)
        else { return nil }
        return kb
    }

    static func summarize(_ samples: [FolderSizeSample]) -> (body: String, proposedFixes: [String]) {
        var lines = ["User folder sizes (approximate, via du):", ""]
        var fixes: [String] = []
        let sorted = samples.sorted {
            ($0.kilobytes ?? -1) > ($1.kilobytes ?? -1)
        }
        for sample in sorted {
            if let gb = sample.gigabytes {
                lines.append(String(format: "  %6.2f GB  %@", gb, sample.name))
                if gb >= 10 {
                    fixes.append(
                        "\(sample.name) is large (\(String(format: "%.1f", gb)) GB). Review and delete what you don’t need (or move to external storage)."
                    )
                }
            } else if let error = sample.error {
                lines.append("  (skipped) \(sample.name) — \(error)")
            } else {
                lines.append("  (unknown) \(sample.name)")
            }
        }
        if fixes.isEmpty {
            fixes.append("No single listed folder looks huge. If disk is still tight, check System Settings → General → Storage and empty Trash.")
        }
        fixes.append("Geek Squad does not delete files for you.")
        return (lines.joined(separator: "\n"), fixes)
    }
}

enum BatteryPowerParser {
    /// Extracts `42%` from typical `pmset -g batt` output.
    static func percent(from text: String) -> Int? {
        for raw in text.split(whereSeparator: \.isNewline) {
            let line = String(raw)
            guard let range = line.range(of: #"(\d+)%"#, options: .regularExpression) else { continue }
            let token = line[range].trimmingCharacters(in: CharacterSet(charactersIn: "%"))
            if let value = Int(token) { return value }
        }
        return nil
    }
}
