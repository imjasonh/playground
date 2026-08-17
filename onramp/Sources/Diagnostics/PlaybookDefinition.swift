import Foundation

/// Preference-domain keys device admins can set via MDM (or `defaults write`)
/// on `io.github.imjasonh.onramp`.
enum PlaybookPreferenceKey {
    static let playbooks = "Playbooks"
    static let playbooksJSON = "PlaybooksJSON"
    static let disabledPlaybookIDs = "DisabledPlaybookIDs"
}

/// Allowlisted probe targets a playbook may override. Custom playbooks cannot
/// add commands — only hostnames/URLs that existing read-only diagnostics accept.
struct PlaybookProbes: Equatable, Hashable, Sendable {
    var dnsHostname: String
    var httpURL: String
    var reachHost: String
    var reachPort: UInt16

    static let defaults = PlaybookProbes(
        dnsHostname: "example.com",
        httpURL: "https://example.com",
        reachHost: "1.1.1.1",
        reachPort: 443
    )
}

/// A playbook the Playbooks tab can run — built-in, MDM-managed, or a local file.
struct PlaybookDefinition: Identifiable, Equatable, Hashable, Sendable {
    enum Source: String, Equatable, Hashable, Sendable {
        case builtIn
        case managed
        case localFile
    }

    var id: String
    var title: String
    var subtitle: String
    var symbolName: String
    /// Ranking lens — custom playbooks pick one of the built-in foci.
    var focus: ConnectivityPlaybookKind
    var source: Source
    var probes: PlaybookProbes
    /// Extra proposed steps shown when the playbook does **not** look healthy.
    /// Display-only; never executed.
    var extraSteps: [String]

    var isBuiltIn: Bool { source == .builtIn }

    var sourceCaption: String? {
        switch source {
        case .builtIn:
            return nil
        case .managed:
            return "Provisioned by device admin"
        case .localFile:
            return "Loaded from this Mac"
        }
    }

    static func builtIn(_ kind: ConnectivityPlaybookKind) -> PlaybookDefinition {
        PlaybookDefinition(
            id: kind.rawValue,
            title: kind.title,
            subtitle: kind.subtitle,
            symbolName: kind.symbolName,
            focus: kind,
            source: .builtIn,
            probes: .defaults,
            extraSteps: []
        )
    }

    static var builtInAll: [PlaybookDefinition] {
        ConnectivityPlaybookKind.allCases.map(builtIn)
    }
}

/// Parses and assembles the playbook list. Invalid admin entries are skipped
/// (no arbitrary commands, only allowlisted probe overrides).
enum PlaybookCatalog {
    static let maxCustomPlaybooks = 32

    /// Built-in playbooks, then valid custom ones (managed overrides local on id clash).
    static func assemble(
        managed: [PlaybookDefinition],
        local: [PlaybookDefinition],
        disabledIDs: Set<String>
    ) -> [PlaybookDefinition] {
        let reserved = Set(ConnectivityPlaybookKind.allCases.map(\.rawValue))
        var builtIn = PlaybookDefinition.builtInAll.filter { !disabledIDs.contains($0.id) }
        if builtIn.isEmpty {
            builtIn = [PlaybookDefinition.builtIn(.cantGetOnline)]
        }

        var byID: [String: PlaybookDefinition] = [:]
        for item in local + managed {
            guard !reserved.contains(item.id), !disabledIDs.contains(item.id) else { continue }
            byID[item.id] = item
        }
        let custom = byID.values.sorted {
            $0.title.localizedCaseInsensitiveCompare($1.title) == .orderedAscending
        }
        return builtIn + Array(custom.prefix(maxCustomPlaybooks))
    }

    /// Live catalog: preference domain (MDM / `defaults write`) plus drop-in files.
    static func load(
        defaults: UserDefaults = .standard,
        fileURLs: [URL]? = nil,
        fileManager: FileManager = .default
    ) -> [PlaybookDefinition] {
        var disabled = Set(defaults.stringArray(forKey: PlaybookPreferenceKey.disabledPlaybookIDs) ?? [])
        var managed: [PlaybookDefinition] = []
        if let array = defaults.array(forKey: PlaybookPreferenceKey.playbooks) {
            managed.append(contentsOf: PlaybookDefinitionParser.parseList(array, source: .managed))
        }
        if let json = defaults.string(forKey: PlaybookPreferenceKey.playbooksJSON) {
            let parsed = PlaybookDefinitionParser.parseJSONString(json, source: .managed)
            managed.append(contentsOf: parsed.playbooks)
            disabled.formUnion(parsed.disabledIDs)
        }

        var local: [PlaybookDefinition] = []
        let urls = fileURLs ?? standardFileURLs(fileManager: fileManager)
        for url in urls {
            guard fileManager.fileExists(atPath: url.path) else { continue }
            guard let data = try? Data(contentsOf: url) else { continue }
            let parsed = PlaybookDefinitionParser.parseFile(data, url: url)
            local.append(contentsOf: parsed.playbooks)
            disabled.formUnion(parsed.disabledIDs)
        }

        return assemble(managed: managed, local: local, disabledIDs: disabled)
    }

    static func standardFileURLs(fileManager: FileManager = .default) -> [URL] {
        let names = ["playbooks.plist", "playbooks.json"]
        var urls: [URL] = []
        let machine = URL(fileURLWithPath: "/Library/Application Support/Onramp", isDirectory: true)
        let user = fileManager.homeDirectoryForCurrentUser
            .appendingPathComponent("Library/Application Support/Onramp", isDirectory: true)
        for folder in [machine, user] {
            for name in names {
                urls.append(folder.appendingPathComponent(name))
            }
        }
        return urls
    }
}

struct PlaybookParseResult: Equatable {
    var playbooks: [PlaybookDefinition]
    var disabledIDs: Set<String>
}

enum PlaybookDefinitionParser {
    static func parseList(_ raw: Any, source: PlaybookDefinition.Source) -> [PlaybookDefinition] {
        guard let items = raw as? [Any] else { return [] }
        return items.compactMap { item in
            guard let dict = item as? [String: Any] else { return nil }
            return parseEntry(dict, source: source)
        }
    }

    static func parseJSONString(
        _ string: String,
        source: PlaybookDefinition.Source
    ) -> PlaybookParseResult {
        let trimmed = string.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty, let data = trimmed.data(using: .utf8) else {
            return PlaybookParseResult(playbooks: [], disabledIDs: [])
        }
        return parseJSONData(data, source: source)
    }

    static func parseFile(_ data: Data, url: URL) -> PlaybookParseResult {
        let source = PlaybookDefinition.Source.localFile
        switch url.pathExtension.lowercased() {
        case "json":
            return parseJSONData(data, source: source)
        case "plist":
            return parsePlistData(data, source: source)
        default:
            let json = parseJSONData(data, source: source)
            if !json.playbooks.isEmpty || !json.disabledIDs.isEmpty {
                return json
            }
            return parsePlistData(data, source: source)
        }
    }

    static func parseEntry(_ raw: [String: Any], source: PlaybookDefinition.Source) -> PlaybookDefinition? {
        guard let id = sanitizeID(stringValue(raw["id"])) else { return nil }
        guard let title = sanitizeTitle(stringValue(raw["title"])) else { return nil }
        let subtitle = sanitizeSubtitle(stringValue(raw["subtitle"])) ?? ""
        let focus = parseFocus(stringValue(raw["focus"]))
        let symbol = sanitizeSymbol(stringValue(raw["symbol"]) ?? stringValue(raw["symbolName"]))
            ?? focus.symbolName
        let probes = parseProbes(raw)
        let extra = parseExtraSteps(raw["extraSteps"] ?? raw["steps"])
        return PlaybookDefinition(
            id: id,
            title: title,
            subtitle: subtitle,
            symbolName: symbol,
            focus: focus,
            source: source,
            probes: probes,
            extraSteps: extra
        )
    }

    static func parseFocus(_ raw: String?) -> ConnectivityPlaybookKind {
        let key = normalizeToken(raw ?? "")
        switch key {
        case "", "cantgetonline", "cant-get-online", "online", "full":
            return .cantGetOnline
        case "vpnbroken", "vpn-broken", "vpn", "vpnconnectedbutbroken":
            return .vpnBroken
        case "dnswrong", "dns-wrong", "dns", "dnsfeelswrong":
            return .dnsWrong
        case "captiveportal", "captive-portal", "captive", "hotel":
            return .captivePortal
        case "somesitesfail", "some-sites-fail", "somesites", "sites":
            return .someSitesFail
        default:
            return .cantGetOnline
        }
    }

    // MARK: - File payloads

    private static func parseJSONData(_ data: Data, source: PlaybookDefinition.Source) -> PlaybookParseResult {
        guard let obj = try? JSONSerialization.jsonObject(with: data) else {
            return PlaybookParseResult(playbooks: [], disabledIDs: [])
        }
        return parseRoot(obj, source: source)
    }

    private static func parsePlistData(_ data: Data, source: PlaybookDefinition.Source) -> PlaybookParseResult {
        guard let obj = try? PropertyListSerialization.propertyList(from: data, options: [], format: nil)
        else {
            return PlaybookParseResult(playbooks: [], disabledIDs: [])
        }
        return parseRoot(obj, source: source)
    }

    private static func parseRoot(_ obj: Any, source: PlaybookDefinition.Source) -> PlaybookParseResult {
        if let array = obj as? [Any] {
            return PlaybookParseResult(playbooks: parseList(array, source: source), disabledIDs: [])
        }
        guard let dict = obj as? [String: Any] else {
            return PlaybookParseResult(playbooks: [], disabledIDs: [])
        }
        let list = dict[PlaybookPreferenceKey.playbooks] ?? dict["playbooks"]
        let playbooks = list.map { parseList($0, source: source) } ?? []
        var disabled = Set<String>()
        if let ids = dict[PlaybookPreferenceKey.disabledPlaybookIDs] ?? dict["disabledPlaybookIDs"] {
            disabled = parseDisabledIDs(ids)
        }
        return PlaybookParseResult(playbooks: playbooks, disabledIDs: disabled)
    }

    static func parseDisabledIDs(_ raw: Any) -> Set<String> {
        if let strings = raw as? [String] {
            return Set(strings.compactMap(sanitizeID))
        }
        if let any = raw as? [Any] {
            return Set(any.compactMap { sanitizeID(stringValue($0)) })
        }
        if let one = stringValue(raw) {
            return Set([one].compactMap(sanitizeID))
        }
        return []
    }

    // MARK: - Field sanitizers

    static func sanitizeID(_ raw: String?) -> String? {
        let trimmed = raw?.trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        guard (1 ... 64).contains(trimmed.count) else { return nil }
        let allowed = CharacterSet.alphanumerics.union(CharacterSet(charactersIn: ".-_"))
        guard trimmed.unicodeScalars.allSatisfy({ allowed.contains($0) }) else { return nil }
        return trimmed
    }

    static func sanitizeTitle(_ raw: String?) -> String? {
        let trimmed = raw?.trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        guard (1 ... 80).contains(trimmed.count) else { return nil }
        guard trimmed.rangeOfCharacter(from: .controlCharacters) == nil else { return nil }
        return trimmed
    }

    static func sanitizeSubtitle(_ raw: String?) -> String? {
        let trimmed = raw?.trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        guard !trimmed.isEmpty else { return nil }
        guard trimmed.count <= 200 else { return String(trimmed.prefix(200)) }
        guard trimmed.rangeOfCharacter(from: .controlCharacters) == nil else { return nil }
        return trimmed
    }

    static func sanitizeSymbol(_ raw: String?) -> String? {
        let trimmed = raw?.trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        guard (1 ... 64).contains(trimmed.count) else { return nil }
        let allowed = CharacterSet.alphanumerics.union(CharacterSet(charactersIn: "."))
        guard trimmed.unicodeScalars.allSatisfy({ allowed.contains($0) }) else { return nil }
        return trimmed
    }

    static func parseProbes(_ raw: [String: Any]) -> PlaybookProbes {
        var probes = PlaybookProbes.defaults
        if let host = NetworkProbeHost.sanitize(stringValue(raw["dnsHostname"]) ?? "") {
            probes.dnsHostname = host
        }
        if let url = parseHTTPURL(stringValue(raw["httpURL"])) {
            probes.httpURL = url
        }
        if let host = NetworkProbeHost.sanitize(stringValue(raw["reachHost"]) ?? "") {
            probes.reachHost = host
        }
        if let port = parsePort(raw["reachPort"]) {
            probes.reachPort = port
        }
        return probes
    }

    static func parseHTTPURL(_ raw: String?) -> String? {
        let trimmed = raw?.trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        guard !trimmed.isEmpty, trimmed.count <= 500 else { return nil }
        guard let url = URL(string: trimmed) else { return nil }
        guard url.scheme == "http" || url.scheme == "https" else { return nil }
        guard let host = url.host, !host.isEmpty else { return nil }
        guard url.user == nil, url.password == nil else { return nil }
        guard NetworkProbeHost.sanitize(host) != nil else { return nil }
        return trimmed
    }

    static func parsePort(_ raw: Any?) -> UInt16? {
        if let n = raw as? Int, (1 ... 65535).contains(n) {
            return UInt16(n)
        }
        if let n = raw as? Int64, (1 ... 65535).contains(n) {
            return UInt16(n)
        }
        if let n = raw as? Double, n == n.rounded(), (1 ... 65535).contains(Int(n)) {
            return UInt16(n)
        }
        if let s = stringValue(raw), let n = Int(s), (1 ... 65535).contains(n) {
            return UInt16(n)
        }
        return nil
    }

    static func parseExtraSteps(_ raw: Any?) -> [String] {
        let items: [String]
        if let strings = raw as? [String] {
            items = strings
        } else if let any = raw as? [Any] {
            items = any.compactMap(stringValue)
        } else if let one = stringValue(raw) {
            items = [one]
        } else {
            items = []
        }
        var seen = Set<String>()
        var out: [String] = []
        for item in items {
            let trimmed = item.trimmingCharacters(in: .whitespacesAndNewlines)
            guard (1 ... 500).contains(trimmed.count) else { continue }
            guard trimmed.rangeOfCharacter(from: .controlCharacters) == nil else { continue }
            guard !RemediationCopy.isNoOp(trimmed) else { continue }
            guard seen.insert(trimmed).inserted else { continue }
            out.append(trimmed)
            if out.count >= 8 { break }
        }
        return out
    }

    private static func stringValue(_ raw: Any?) -> String? {
        if let s = raw as? String { return s }
        if let n = raw as? NSNumber { return n.stringValue }
        return nil
    }

    private static func normalizeToken(_ raw: String) -> String {
        raw.trimmingCharacters(in: .whitespacesAndNewlines)
            .lowercased()
            .replacingOccurrences(of: "_", with: "-")
            .replacingOccurrences(of: " ", with: "-")
            .replacingOccurrences(of: "'", with: "")
    }
}
