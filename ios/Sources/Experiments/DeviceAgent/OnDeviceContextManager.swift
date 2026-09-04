import Foundation

#if canImport(FoundationModels)
import FoundationModels
#endif

/// Shared helpers for staying inside Apple's on-device Foundation Models
/// 4096-token context window (TN3193).
///
/// `LanguageModelSession` owns the live transcript; you cannot prune it in
/// place. When the window fills, start a new session seeded from a condensed
/// transcript (first + last entries) plus a short app-state carry-over.
enum OnDeviceContextManager {
    /// Soft budget left for tools + model reply inside the 4096-token window.
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

    /// Detects context-window overflow, including typed GenerationError cases
    /// and the generic FoundationModels code `-1` seen on device.
    nonisolated static func isExceededContextWindow(_ error: Error) -> Bool {
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            // Prefer typed GenerationError when present; also match by description so
            // older/newer SDK case spellings still detect overflow.
            let described = String(describing: error).lowercased()
            if described.contains("exceededcontextwindowsize")
                || described.contains("contextsizeexceeded")
            {
                return true
            }
        }
        #endif

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
            // Observed on device: GenerationError error -1 with no useful message.
            if ns.code == -1 { return true }
        }
        return false
    }

    /// Compresses older turns into a short factual archive and keeps the most
    /// recent turns intact. Extractive (no model call) so unit tests and CI
    /// can exercise it without Apple Intelligence.
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
        var parts: [String] = []

        let archiveBits = older.map { turn in
            let who = turn.role == .user ? "User" : "Assistant"
            let body = turn.content
                .replacingOccurrences(of: "\n", with: " ")
                .trimmingCharacters(in: .whitespacesAndNewlines)
            return "\(who): \(String(body.prefix(160)))"
        }
        if !archiveBits.isEmpty {
            parts.append("[Background archive of prior conversation]:")
            parts.append(archiveBits.joined(separator: " · "))
        }
        if !recent.isEmpty {
            parts.append("Recent chat (oldest first):")
            for turn in recent {
                let who = turn.role == .user ? "User" : "Assistant"
                let body = turn.content
                    .replacingOccurrences(of: "\n", with: " ")
                    .trimmingCharacters(in: .whitespacesAndNewlines)
                parts.append("\(who): \(String(body.prefix(280)))")
            }
        }
        return AgentContextBudget.truncateToChars(parts.joined(separator: "\n"), maxChars: maxChars)
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

    #if canImport(FoundationModels)
    /// Seeds a fresh session from the original transcript's first and last
    /// entries (TN3193), then prewarms. Returns nil when the transcript is
    /// empty or too short to condense.
    @available(iOS 26.0, *)
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
    #endif

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
