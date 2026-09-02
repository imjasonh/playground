import Foundation

/// Tracks how full the on-device Foundation Model context window is, and caps
/// text so Device Agent does not hit the hard limit mid-turn.
///
/// Apple's on-device model window is 4096 tokens. English is roughly 3-4
/// characters per token; this budget uses 3 so estimates stay slightly high.
struct AgentContextBudget: Equatable {
    static let defaultWindowTokens = 4096
    /// Conservative chars/token so we under-fill rather than overshoot.
    static let charsPerToken = 3
    /// Leave room for the model's final answer.
    static let responseReserveTokens = 512
    /// Rough cost of browser tool schemas registered with the session.
    static let defaultToolsReserveTokens = 1200
    /// Compact into a fresh session at or above this fill fraction.
    static let compactThreshold = 0.72
    /// Refuse further large tool payloads at or above this fill fraction.
    static let hardStopFraction = 0.90
    /// Default max characters of page text scraped for extraction / dump.
    static let defaultSnapshotTextChars = 1800
    /// Max characters returned to the model for a single tool result.
    static let defaultModelToolResultChars = 2400

    var windowTokens: Int
    var instructionsTokens: Int
    var toolsReserveTokens: Int
    /// Tokens attributed to prompts, tool I/O, and model replies in this session.
    var usedTokens: Int

    init(
        windowTokens: Int = Self.defaultWindowTokens,
        instructionsTokens: Int = 0,
        toolsReserveTokens: Int = Self.defaultToolsReserveTokens,
        usedTokens: Int = 0
    ) {
        self.windowTokens = max(512, windowTokens)
        self.instructionsTokens = max(0, instructionsTokens)
        self.toolsReserveTokens = max(0, toolsReserveTokens)
        self.usedTokens = max(0, usedTokens)
    }

    /// Instructions + tool schemas + turn content, against the full window.
    var committedTokens: Int {
        min(windowTokens, instructionsTokens + toolsReserveTokens + usedTokens)
    }

    var remainingTokens: Int {
        max(0, windowTokens - committedTokens - Self.responseReserveTokens)
    }

    /// 0...1 fill level for the UI (response reserve still counts as free).
    var fractionUsed: Double {
        guard windowTokens > 0 else { return 1 }
        return min(1, Double(committedTokens) / Double(windowTokens))
    }

    var percentUsed: Int {
        Int((fractionUsed * 100).rounded(.down))
    }

    var needsCompact: Bool {
        fractionUsed >= Self.compactThreshold
    }

    var isNearHardStop: Bool {
        fractionUsed >= Self.hardStopFraction
    }

    mutating func resetBaseline(instructions: String, toolsReserveTokens: Int = Self.defaultToolsReserveTokens) {
        self.instructionsTokens = Self.estimateTokens(instructions)
        self.toolsReserveTokens = toolsReserveTokens
        self.usedTokens = 0
    }

    mutating func addText(_ text: String) {
        usedTokens += Self.estimateTokens(text)
        if usedTokens < 0 { usedTokens = 0 }
    }

    mutating func addTokens(_ tokens: Int) {
        usedTokens += max(0, tokens)
    }

    static func estimateTokens(_ text: String) -> Int {
        let count = text.utf8.count
        guard count > 0 else { return 0 }
        return max(1, (count + charsPerToken - 1) / charsPerToken)
    }

    static func maxChars(forTokens tokens: Int) -> Int {
        max(0, tokens * charsPerToken)
    }

    /// Caps scrape text length for this turn from remaining budget.
    func snapshotTextCharBudget(default defaultChars: Int = Self.defaultSnapshotTextChars) -> Int {
        let fromRemaining = Self.maxChars(forTokens: max(80, remainingTokens / 3))
        return max(400, min(defaultChars, fromRemaining))
    }

    /// Caps the model-facing tool result string.
    func modelToolResultCharBudget(default defaultChars: Int = Self.defaultModelToolResultChars) -> Int {
        let fromRemaining = Self.maxChars(forTokens: max(40, remainingTokens / 2))
        return max(280, min(defaultChars, fromRemaining))
    }

    /// Truncates `text` to about `maxTokens` tokens, appending an ellipsis marker.
    static func truncate(_ text: String, maxTokens: Int) -> String {
        let maxChars = maxChars(forTokens: maxTokens)
        return truncateToChars(text, maxChars: maxChars)
    }

    static func truncateToChars(_ text: String, maxChars: Int) -> String {
        guard maxChars > 0 else { return "" }
        guard text.count > maxChars else { return text }
        if maxChars <= 1 { return "…" }
        let end = text.index(text.startIndex, offsetBy: maxChars - 1)
        return String(text[..<end]) + "…"
    }

    /// Compact tool payload for the LanguageModelSession (omit bulky page text).
    static func modelFacingSnapshot(
        title: String,
        url: String,
        elements: [String],
        headings: [String],
        extractedFindings: [String],
        maxChars: Int,
        extractionNote: String? = nil
    ) -> String {
        var lines: [String] = [
            "title: \(title)",
            "url: \(url)",
        ]
        if let extractionNote, !extractionNote.isEmpty {
            lines.append("note: \(extractionNote)")
        }
        if !extractedFindings.isEmpty {
            let label = (extractionNote?.isEmpty == false) ? "approximateFindings" : "extractedFindings"
            lines.append("\(label):")
            lines.append(contentsOf: extractedFindings.map { "• \($0)" })
        }
        let elementCap = min(40, elements.count)
        if elementCap > 0 {
            lines.append("elements (\(elements.count), showing \(elementCap)):")
            lines.append(contentsOf: elements.prefix(elementCap))
        }
        if !headings.isEmpty {
            lines.append("headings:")
            lines.append(contentsOf: headings.prefix(12).map { "- \($0)" })
        }
        lines.append("Page text omitted from model context; use findings and element refs.")
        return truncateToChars(lines.joined(separator: "\n"), maxChars: maxChars)
    }

    /// Short carry-over for a compacted session so follow-ups keep page context.
    /// Omits findings when `findingsURL` does not match the current page `url`.
    static func compactionCarryOver(
        url: String?,
        title: String?,
        findings: [String],
        findingsURL: String? = nil,
        recentUserPrompts: [String]
    ) -> String {
        var parts: [String] = ["Compacted prior context (keep using the open browser tab):"]
        if let title, !title.isEmpty {
            parts.append("Page title: \(title)")
        }
        if let url, !url.isEmpty {
            parts.append("Page URL: \(url)")
        }
        let findingsMatchCurrentPage: Bool = {
            guard !findings.isEmpty else { return false }
            guard let findingsURL, !findingsURL.isEmpty else { return true }
            return findingsURL == url
        }()
        if findingsMatchCurrentPage {
            parts.append("Latest page findings:")
            parts.append(contentsOf: findings.prefix(8).map { "• \($0)" })
        }
        if !recentUserPrompts.isEmpty {
            parts.append("Recent user asks:")
            parts.append(contentsOf: recentUserPrompts.suffix(3).map { "- \($0)" })
        }
        return truncateToChars(parts.joined(separator: "\n"), maxChars: 1200)
    }
}

/// Published snapshot of context fill for the Device Agent UI.
struct AgentContextUsage: Equatable {
    var usedTokens: Int
    var windowTokens: Int
    var fractionUsed: Double
    var percentUsed: Int
    var didCompact: Bool

    static let empty = AgentContextUsage(
        usedTokens: 0,
        windowTokens: AgentContextBudget.defaultWindowTokens,
        fractionUsed: 0,
        percentUsed: 0,
        didCompact: false
    )

    init(budget: AgentContextBudget, didCompact: Bool = false) {
        usedTokens = budget.committedTokens
        windowTokens = budget.windowTokens
        fractionUsed = budget.fractionUsed
        percentUsed = budget.percentUsed
        self.didCompact = didCompact
    }

    init(usedTokens: Int, windowTokens: Int, fractionUsed: Double, percentUsed: Int, didCompact: Bool) {
        self.usedTokens = usedTokens
        self.windowTokens = windowTokens
        self.fractionUsed = fractionUsed
        self.percentUsed = percentUsed
        self.didCompact = didCompact
    }

    var accessibilityLabel: String {
        "Model context \(percentUsed) percent full"
    }
}
