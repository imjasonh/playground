import Foundation
import FoundationModels

/// Compact theme the construction loop ranks against and puts in each Laya
/// state. Apple Intelligence can write this once per Build / Fill; otherwise
/// tokens come from the prompt and the units already on the list.
struct ArmyListThemeBrief: Equatable {
    enum Source: String, Equatable {
        case none
        case prompt
        case roster
        case foundationModels
    }

    var prompt: String
    var tokens: [String]
    var summary: String
    var source: Source

    /// Ranking string for ``ArmyListPalette``. Prompt words stay so a typed
    /// name still matches, and brief tokens cover AFM expansions such as
    /// "bike" for "White Scars fast attack".
    var rankingText: String {
        var parts: [String] = []
        let trimmed = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        if !trimmed.isEmpty { parts.append(trimmed) }
        if !tokens.isEmpty { parts.append(tokens.joined(separator: " ")) }
        return parts.joined(separator: " ")
    }

    /// One line for the Laya snapshot. Prefers the AFM sentence.
    var snapshotTheme: String {
        let line = summary.trimmingCharacters(in: .whitespacesAndNewlines)
        if !line.isEmpty { return line }
        if !tokens.isEmpty { return tokens.joined(separator: " ") }
        return prompt.trimmingCharacters(in: .whitespacesAndNewlines)
    }
}

/// Builds ``ArmyListThemeBrief``. Tests replace the live model with
/// ``testOverride`` and turn the model off with ``foundationModelsEnabled``.
enum ArmyListThemeBriefBuilder {
    static let maxTokens = 8
    static let maxSummaryCharacters = 80

    /// When false, skip Apple Intelligence (unit tests).
    static var foundationModelsEnabled = true

    /// When set, ``make`` returns this and does not call the model.
    static var testOverride: ((Input) -> ArmyListThemeBrief)?

    struct Input: Equatable {
        var factionName: String
        var prompt: String
        var rosterNames: [String]
    }

    static func make(
        catalog: ArmyCatalog,
        factionID: String,
        prompt: String,
        list: ArmyListDocument
    ) async -> ArmyListThemeBrief {
        let factionName = catalog.faction(id: factionID)?.name ?? factionID
        let rosterNames = list.units.prefix(12).map { unit in
            catalog.datasheet(id: unit.datasheetID)?.name ?? unit.datasheetID
        }
        let input = Input(factionName: factionName, prompt: prompt, rosterNames: Array(rosterNames))
        if let testOverride {
            return sanitize(testOverride(input), prompt: prompt)
        }

        let fallback = heuristic(catalog: catalog, prompt: prompt, list: list)
        guard foundationModelsEnabled, shouldAskFoundationModels(prompt: prompt, list: list) else {
            return fallback
        }
        if let modelBrief = await foundationModelBrief(input: input) {
            return merge(model: modelBrief, heuristic: fallback, prompt: prompt)
        }
        return fallback
    }

    /// Prompt words plus tokens taken from units already on the list.
    static func heuristic(
        catalog: ArmyCatalog,
        prompt: String,
        list: ArmyListDocument
    ) -> ArmyListThemeBrief {
        let promptTokens = ArmyListPalette.themeTokens(prompt)
        let fromRoster = rosterTokens(list: list, catalog: catalog)
        var tokens: [String] = []
        for token in promptTokens + fromRoster where !tokens.contains(token) {
            tokens.append(token)
            if tokens.count >= maxTokens { break }
        }
        let trimmedPrompt = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        let source: ArmyListThemeBrief.Source
        if !promptTokens.isEmpty {
            source = .prompt
        } else if !fromRoster.isEmpty {
            source = .roster
        } else {
            source = .none
        }
        let summary: String
        if !trimmedPrompt.isEmpty {
            summary = clipSummary(trimmedPrompt)
        } else if !tokens.isEmpty {
            summary = clipSummary("Matches the roster: " + tokens.joined(separator: ", "))
        } else {
            summary = ""
        }
        return ArmyListThemeBrief(
            prompt: trimmedPrompt,
            tokens: tokens,
            summary: summary,
            source: source
        )
    }

    static func rosterTokens(list: ArmyListDocument, catalog: ArmyCatalog) -> [String] {
        var counts: [String: Int] = [:]
        for unit in list.units {
            guard let sheet = catalog.datasheet(id: unit.datasheetID) else { continue }
            for token in sheetTokens(sheet) {
                counts[token, default: 0] += 1
            }
        }
        return counts
            .sorted { lhs, rhs in
                if lhs.value != rhs.value { return lhs.value > rhs.value }
                return lhs.key < rhs.key
            }
            .prefix(maxTokens)
            .map(\.key)
    }

    static func sheetTokens(_ sheet: DatasheetDefinition) -> [String] {
        let keywords = sheet.keywords.filter { !$0.lowercased().hasPrefix("faction:") }
        let raw = ([sheet.name] + keywords + sheet.themeKeywords).joined(separator: " ")
        return ArmyListPalette.themeTokens(raw).filter { !rosterStopWords.contains($0) }
    }

    /// Generic catalog words that do not describe a theme when taken from a roster.
    static let rosterStopWords: Set<String> = [
        "squad", "squads", "unit", "units", "team", "teams", "grenades",
        "infantry", "keyword", "keywords",
    ]

    private static func shouldAskFoundationModels(prompt: String, list: ArmyListDocument) -> Bool {
        let trimmed = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        return !trimmed.isEmpty || !list.units.isEmpty
    }

    private static func merge(
        model: ArmyListThemeBrief,
        heuristic: ArmyListThemeBrief,
        prompt: String
    ) -> ArmyListThemeBrief {
        var tokens: [String] = []
        for token in model.tokens + heuristic.tokens where !tokens.contains(token) {
            tokens.append(token)
            if tokens.count >= maxTokens { break }
        }
        let summary = model.summary.isEmpty ? heuristic.summary : model.summary
        return sanitize(
            ArmyListThemeBrief(
                prompt: prompt.trimmingCharacters(in: .whitespacesAndNewlines),
                tokens: tokens,
                summary: summary,
                source: .foundationModels
            ),
            prompt: prompt
        )
    }

    private static func sanitize(_ brief: ArmyListThemeBrief, prompt: String) -> ArmyListThemeBrief {
        var tokens: [String] = []
        for raw in brief.tokens {
            for token in ArmyListPalette.themeTokens(raw) where !tokens.contains(token) {
                tokens.append(token)
                if tokens.count >= maxTokens { break }
            }
            if tokens.count >= maxTokens { break }
        }
        return ArmyListThemeBrief(
            prompt: prompt.trimmingCharacters(in: .whitespacesAndNewlines),
            tokens: tokens,
            summary: clipSummary(brief.summary),
            source: brief.source
        )
    }

    static func clipSummary(_ raw: String) -> String {
        var text = raw
            .replacingOccurrences(of: "\"", with: "")
            .replacingOccurrences(of: "\n", with: " ")
            .replacingOccurrences(of: #"\s+"#, with: " ", options: .regularExpression)
            .trimmingCharacters(in: .whitespacesAndNewlines)
        if text.count > maxSummaryCharacters {
            let end = text.index(text.startIndex, offsetBy: maxSummaryCharacters)
            text = String(text[..<end]).trimmingCharacters(in: .whitespaces)
            if let lastSpace = text.lastIndex(of: " "), lastSpace > text.startIndex {
                text = String(text[..<lastSpace])
            }
        }
        return text
    }

    private static func foundationModelBrief(input: Input) async -> ArmyListThemeBrief? {
        let model = SystemLanguageModel.default
        guard model.isAvailable else { return nil }

        let session = LanguageModelSession(instructions: """
            You write a short army-list theme for a 40K builder.
            Return 4 to 8 catalog unit-type tokens (bike, outrider, jump, monster, swarm).
            Prefer datasheet words over slogans.
            Write one line that names the theme from the prompt if it is present, otherwise from the roster.
            """)
        do {
            let response = try await session.respond(to: prompt(for: input), generating: ModelTheme.self)
            let content = response.content
            return ArmyListThemeBrief(
                prompt: input.prompt,
                tokens: content.tokens,
                summary: content.summary,
                source: .foundationModels
            )
        } catch {
            return nil
        }
    }

    static func prompt(for input: Input) -> String {
        var lines: [String] = [
            "Faction: \(input.factionName)",
            "Prompt: \(input.prompt.isEmpty ? "(none)" : input.prompt)",
        ]
        if input.rosterNames.isEmpty {
            lines.append("Roster: (empty)")
        } else {
            lines.append("Roster: " + input.rosterNames.joined(separator: ", "))
        }
        lines.append("Return tokens that match datasheet names or roles, plus one summary line.")
        return lines.joined(separator: "\n")
    }

    @Generable
    struct ModelTheme {
        @Guide(.maximumCount(8))
        @Guide(description: "4 to 8 catalog unit-type words")
        var tokens: [String]
        @Guide(description: "One line naming the list theme")
        var summary: String
    }
}
