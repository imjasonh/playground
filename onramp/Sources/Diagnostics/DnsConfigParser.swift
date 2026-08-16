import Foundation

/// Parses `scutil --dns` style output into a compact summary.
enum DnsConfigParser {
    struct Summary: Equatable, Sendable {
        var resolvers: [String]
        var searchDomains: [String]
        var scopedResolverCount: Int

        var description: String {
            var lines: [String] = []
            if resolvers.isEmpty {
                lines.append("Resolvers: (none found)")
            } else {
                lines.append("Resolvers:")
                for r in resolvers.prefix(12) {
                    lines.append("  - \(r)")
                }
                if resolvers.count > 12 {
                    lines.append("  … +\(resolvers.count - 12) more")
                }
            }
            if !searchDomains.isEmpty {
                lines.append("Search domains: \(searchDomains.joined(separator: ", "))")
            }
            lines.append("Scoped resolver blocks: \(scopedResolverCount)")
            return lines.joined(separator: "\n")
        }
    }

    static func parse(_ text: String) -> Summary {
        var resolvers: [String] = []
        var search: [String] = []
        var scoped = 0
        var seenResolver = Set<String>()
        var seenSearch = Set<String>()

        for raw in text.split(whereSeparator: \.isNewline) {
            let line = raw.trimmingCharacters(in: .whitespaces)
            if line.hasPrefix("resolver #") {
                scoped += 1
                continue
            }
            if line.hasPrefix("nameserver["), let value = valueAfterColon(line) {
                if seenResolver.insert(value).inserted {
                    resolvers.append(value)
                }
            } else if line.hasPrefix("search domain["), let value = valueAfterColon(line) {
                if seenSearch.insert(value).inserted {
                    search.append(value)
                }
            }
        }

        return Summary(
            resolvers: resolvers,
            searchDomains: search,
            scopedResolverCount: scoped
        )
    }

    private static func valueAfterColon(_ line: String) -> String? {
        guard let idx = line.firstIndex(of: ":") else { return nil }
        let value = line[line.index(after: idx)...].trimmingCharacters(in: .whitespaces)
        return value.isEmpty ? nil : value
    }
}
