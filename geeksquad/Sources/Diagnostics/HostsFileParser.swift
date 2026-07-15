import Foundation

/// Parses `/etc/hosts` into non-comment mappings, flagging surprising overrides.
enum HostsFileParser {
    struct Entry: Equatable, Sendable {
        var address: String
        var names: [String]
    }

    struct Summary: Equatable, Sendable {
        var entries: [Entry]
        var surprising: [Entry]

        var description: String {
            if entries.isEmpty {
                return "No host mappings (only comments/blank lines)."
            }
            var lines = ["Mappings (\(entries.count)):"]
            for e in entries.prefix(40) {
                lines.append("  \(e.address)  \(e.names.joined(separator: " "))")
            }
            if entries.count > 40 {
                lines.append("  … +\(entries.count - 40) more")
            }
            if !surprising.isEmpty {
                lines.append("")
                lines.append("Possibly surprising overrides:")
                for e in surprising {
                    lines.append("  \(e.address)  \(e.names.joined(separator: " "))")
                }
            }
            return lines.joined(separator: "\n")
        }
    }

    private static let boringNames: Set<String> = [
        "localhost", "broadcasthost", "localhost.localdomain"
    ]

    static func parse(_ text: String) -> Summary {
        var entries: [Entry] = []
        for raw in text.split(whereSeparator: \.isNewline) {
            var line = String(raw)
            if let hash = line.firstIndex(of: "#") {
                line = String(line[..<hash])
            }
            line = line.trimmingCharacters(in: .whitespaces)
            guard !line.isEmpty else { continue }
            let parts = line.split(whereSeparator: \.isWhitespace).map(String.init)
            guard parts.count >= 2 else { continue }
            entries.append(Entry(address: parts[0], names: Array(parts.dropFirst())))
        }

        let surprising = entries.filter { entry in
            let interesting = entry.names.contains { !boringNames.contains($0.lowercased()) }
            let loopback = entry.address == "127.0.0.1" || entry.address == "::1"
            // Flag non-default names on loopback, or any non-loopback custom hosts.
            return interesting && (loopback || !entry.address.hasPrefix("255."))
        }.filter { entry in
            // Keep default localhost lines out of "surprising".
            !(entry.names.map { $0.lowercased() }.allSatisfy { boringNames.contains($0) })
        }

        return Summary(entries: entries, surprising: surprising)
    }
}
