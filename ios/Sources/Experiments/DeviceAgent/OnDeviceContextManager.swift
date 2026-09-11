import Foundation
import FoundationModels

/// Shared helpers for staying inside the active Foundation Model's context
/// window (TN3193).
///
/// `LanguageModelSession` owns the live transcript; you cannot prune it in
/// place. When the window fills, start a new session seeded from a condensed
/// transcript (first + last entries) plus a short app-state carry-over.
enum OnDeviceContextManager {
    /// Soft budget left for tools and the model reply.
    static let safetyBufferTokens = 1_500
    /// Cap for rolling-summary / carry-over text injected after compact.
    static let carryOverMaxChars = 1_400
    /// How many recent user/assistant turns to keep verbatim in a summary.
    static let recentTurnsToKeep = 4

    /// One chat turn used when building an extractive rolling summary.
    struct Turn: Equatable {
        enum Role: String, Equatable {
            case user
            case assistant
        }

        var role: Role
        var content: String
    }

    /// Detects typed context-window failures and wrapped errors that retain a
    /// context-size description.
    nonisolated static func isExceededContextWindow(_ error: Error) -> Bool {
        if let modelError = error as? LanguageModelError,
           case .contextSizeExceeded(_) = modelError
        {
            return true
        }
        let described = String(describing: error).lowercased()
        if described.contains("exceededcontextwindowsize")
            || described.contains("contextsizeexceeded")
        {
            return true
        }

        let text = error.localizedDescription.lowercased()
        if text.contains("context window")
            || text.contains("exceededcontext")
            || text.contains("contextsizeexceeded")
            || text.contains("context size exceeded")
        {
            return true
        }
        let ns = error as NSError
        let domain = ns.domain.lowercased()
        if domain.contains("foundationmodels") {
            if text.contains("context") { return true }
        }
        return false
    }

    /// Compresses older turns into a short factual archive and keeps the most
    /// recent turns intact. Extractive (no model call) so unit tests and CI
    /// can exercise it without Apple Intelligence.
    ///
    /// Recent turns are reserved first so a tight `maxChars` never drops the
    /// latest user ask (truncate-from-start would otherwise eat the suffix).
    nonisolated static func rollingSummary(
        turns: [Turn],
        recentCount: Int = recentTurnsToKeep,
        maxChars: Int = carryOverMaxChars
    ) -> String {
        guard !turns.isEmpty else { return "" }
        let keep = max(0, recentCount)
        if turns.count <= keep {
            return formatRecent(Array(turns), maxChars: maxChars)
        }

        let older = Array(turns.dropLast(keep))
        let recent = Array(turns.suffix(keep))

        var recentParts: [String] = ["Recent chat (oldest first):"]
        for turn in recent {
            let who = turn.role == .user ? "User" : "Assistant"
            let body = turn.content
                .replacingOccurrences(of: "\n", with: " ")
                .trimmingCharacters(in: .whitespacesAndNewlines)
            recentParts.append("\(who): \(String(body.prefix(280)))")
        }
        let recentBlock = recentParts.joined(separator: "\n")

        // Always keep recent turns; shrink the archive into whatever room remains.
        let recentBudget = min(maxChars, max(recentBlock.count, maxChars / 2))
        let recentText = AgentContextBudget.truncateToChars(recentBlock, maxChars: recentBudget)
        let archiveBudget = max(0, maxChars - recentText.count - 1)

        var archiveText = ""
        if archiveBudget > 40, !older.isEmpty {
            let archiveBits = older.map { turn in
                let who = turn.role == .user ? "User" : "Assistant"
                let body = turn.content
                    .replacingOccurrences(of: "\n", with: " ")
                    .trimmingCharacters(in: .whitespacesAndNewlines)
                return "\(who): \(String(body.prefix(160)))"
            }
            let archiveBlock = """
            [Background archive of prior conversation]:
            \(archiveBits.joined(separator: " · "))
            """
            archiveText = AgentContextBudget.truncateToChars(archiveBlock, maxChars: archiveBudget)
        }

        if archiveText.isEmpty {
            return AgentContextBudget.truncateToChars(recentText, maxChars: maxChars)
        }
        return AgentContextBudget.truncateToChars(
            archiveText + "\n" + recentText,
            maxChars: maxChars
        )
    }

    /// Prefixes a carry-over block onto the next model prompt when instructions
    /// already came from a rehydrated transcript.
    nonisolated static func promptWithCarryOver(prompt: String, carryOver: String) -> String {
        let note = carryOver.trimmingCharacters(in: .whitespacesAndNewlines)
        let body = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !note.isEmpty else { return body }
        guard !body.isEmpty else { return note }
        return AgentContextBudget.truncateToChars(
            """
            Context from before compaction:
            \(note)

            Latest user message:
            \(body)
            """,
            maxChars: max(body.count + 200, carryOverMaxChars + body.count)
        )
    }

    /// Seeds a fresh session from the original transcript's first and last
    /// entries (TN3193), then prewarms. Returns nil when the transcript is
    /// empty or too short to condense.
    static func rehydratedSession(
        from original: LanguageModelSession,
        tools: [any Tool]
    ) -> LanguageModelSession? {
        let allEntries = Array(original.transcript)
        guard let first = allEntries.first else { return nil }
        let condensed: [Transcript.Entry]
        if allEntries.count == 1 {
            condensed = [first]
        } else if let last = allEntries.last {
            condensed = [first, last]
        } else {
            return nil
        }
        let transcript = Transcript(entries: condensed)
        let session = LanguageModelSession(tools: tools, transcript: transcript)
        session.prewarm()
        return session
    }

    private nonisolated static func formatRecent(_ turns: [Turn], maxChars: Int) -> String {
        var parts: [String] = ["Recent chat (oldest first):"]
        for turn in turns {
            let who = turn.role == .user ? "User" : "Assistant"
            let body = turn.content
                .replacingOccurrences(of: "\n", with: " ")
                .trimmingCharacters(in: .whitespacesAndNewlines)
            parts.append("\(who): \(String(body.prefix(280)))")
        }
        return AgentContextBudget.truncateToChars(parts.joined(separator: "\n"), maxChars: maxChars)
    }
}
