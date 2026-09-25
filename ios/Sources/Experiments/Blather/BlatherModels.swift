import Foundation

/// One saved Blather episode: the topic, later directions, and the audio files
/// already synthesized on this device.
struct BlatherEpisode: Codable, Equatable, Identifiable {
    var id: UUID
    var topic: String
    var createdAt: Date
    var updatedAt: Date
    var directions: [String]
    var segments: [BlatherSegment]
}

/// A stretch of speech written to one audio file.
///
/// `duration` is the audible length. A redirect can shorten it so playback
/// stops before the rest of the file, which was generated before the direction.
struct BlatherSegment: Codable, Equatable, Identifiable {
    var id: UUID
    var text: String
    var fileName: String
    var duration: TimeInterval
}

/// Row in the saved-audio list.
struct BlatherEpisodeSummary: Equatable, Identifiable {
    var id: UUID
    var topic: String
    var updatedAt: Date
    var duration: TimeInterval
}

/// One file the player can queue, with the audible length rather than the
/// full file length.
struct BlatherPlayable: Equatable {
    var url: URL
    var duration: TimeInterval
}

/// Playback speeds the player offers. 1× is normal speech.
enum BlatherSpeed: Double, CaseIterable, Identifiable, Hashable {
    case x1 = 1
    case x1_5 = 1.5
    case x1_75 = 1.75
    case x2 = 2

    var id: Double { rawValue }

    var label: String {
        switch self {
        case .x1: "1×"
        case .x1_5: "1.5×"
        case .x1_75: "1.75×"
        case .x2: "2×"
        }
    }

    /// Snaps a lock-screen rate to the nearest offered speed.
    static func nearest(_ rate: Double) -> BlatherSpeed {
        allCases.min { abs($0.rawValue - rate) < abs($1.rawValue - rate) } ?? .x1
    }
}

/// Segments kept after a redirect, plus the files that should be deleted.
struct BlatherCut: Equatable {
    var segments: [BlatherSegment]
    var removedFileNames: [String]
    var playhead: TimeInterval
}

/// Spoken text the model is asked for, and the playback timeline around it.
enum BlatherScript {
    /// Stable session instructions. Kept short so they do not eat the
    /// 4096-token window (TN3193).
    static let instructions = """
    Write spoken explainer audio for one listener.
    Use two or three short paragraphs, about 160 words.
    No titles, markdown, lists, stage directions, or sound cues.
    After the opening, do not greet the listener again.
    End on a complete sentence.
    """

    /// Cap applied after cleaning so one reply cannot fill the context window.
    static let maxSpeechCharacters = 1_400

    static func opening(topic: String, directions: [String]) -> String {
        var lines = [
            "Topic: \(clip(topic))",
            "Start the explainer. Speak to one listener. End on a complete sentence.",
        ]
        if let directions = directionBlock(directions) {
            lines.append(directions)
        }
        return lines.joined(separator: "\n")
    }

    static func continuation(topic: String, directions: [String], tail: String) -> String {
        var lines = [
            "Topic: \(clip(topic))",
            "Continue the explainer from this ending. Do not repeat it:",
            clip(tail, maxCharacters: 480),
            "End on a complete sentence.",
        ]
        if let directions = directionBlock(directions) {
            lines.append(directions)
        }
        return lines.joined(separator: "\n")
    }

    /// Last stretch of speech, starting on a sentence boundary when one fits.
    static func tail(of speech: String, maxCharacters: Int = 480) -> String {
        let trimmed = speech.trimmingCharacters(in: .whitespacesAndNewlines)
        guard trimmed.count > maxCharacters else { return trimmed }
        let start = trimmed.index(trimmed.endIndex, offsetBy: -maxCharacters)
        let slice = trimmed[start...]
        if let mark = slice.firstIndex(where: { $0 == "." || $0 == "!" || $0 == "?" }) {
            let after = trimmed.index(after: mark)
            if after < trimmed.endIndex {
                let rest = String(trimmed[after...]).trimmingCharacters(in: .whitespacesAndNewlines)
                if !rest.isEmpty { return rest }
            }
        }
        return String(slice).trimmingCharacters(in: .whitespacesAndNewlines)
    }

    /// Strips markup the model sometimes adds so speech synthesis reads prose.
    static func clean(_ raw: String) -> String {
        var text = raw.replacingOccurrences(of: "\r\n", with: "\n")
        text = text.replacingOccurrences(of: "```", with: "")
        let lines = text.split(separator: "\n", omittingEmptySubsequences: false).map { rawLine -> String in
            var line = String(rawLine).trimmingCharacters(in: .whitespaces)
            line = line.replacingOccurrences(of: "**", with: "")
            while line.hasPrefix("#") {
                line = String(line.dropFirst()).trimmingCharacters(in: .whitespaces)
            }
            if line.hasPrefix("> ") {
                line = String(line.dropFirst(2))
            }
            if line.hasPrefix("- ") || line.hasPrefix("* ") {
                line = String(line.dropFirst(2))
            }
            for label in ["Host:", "Narrator:", "Speaker:"] where line.hasPrefix(label) {
                line = String(line.dropFirst(label.count)).trimmingCharacters(in: .whitespaces)
            }
            if line.hasPrefix("["), line.hasSuffix("]"), line.count > 1 {
                return ""
            }
            if line.hasPrefix("("), line.hasSuffix(")"), line.count > 2, line.count < 48 {
                return ""
            }
            return line.split(whereSeparator: \.isWhitespace).joined(separator: " ")
        }
        let paragraphs = paragraphs(from: lines)
        var joined = paragraphs.joined(separator: "\n\n")
        joined = trimWrappingQuotes(joined)
        joined = clipToSentences(joined, maxCharacters: maxSpeechCharacters)
        return joined.trimmingCharacters(in: .whitespacesAndNewlines)
    }

    private static func directionBlock(_ directions: [String]) -> String? {
        let lines = directions.suffix(4).map { clip($0, maxCharacters: 200) }.filter { !$0.isEmpty }
        guard !lines.isEmpty else { return nil }
        return "Listener directions, oldest first:\n" + lines.joined(separator: "\n")
    }

    private static func clip(_ text: String, maxCharacters: Int = 280) -> String {
        let trimmed = text.trimmingCharacters(in: .whitespacesAndNewlines)
        return AgentContextBudget.truncateToChars(trimmed, maxChars: maxCharacters)
    }

    private static func paragraphs(from lines: [String]) -> [String] {
        var paragraphs: [String] = []
        var current: [String] = []
        func flush() {
            let text = current.joined(separator: " ").trimmingCharacters(in: .whitespacesAndNewlines)
            if !text.isEmpty {
                paragraphs.append(text)
            }
            current = []
        }
        for line in lines {
            if line.isEmpty {
                flush()
            } else {
                current.append(line)
            }
        }
        flush()
        return paragraphs
    }

    private static func trimWrappingQuotes(_ text: String) -> String {
        var value = text.trimmingCharacters(in: .whitespacesAndNewlines)
        let pairs: [(Character, Character)] = [("\"", "\""), ("“", "”")]
        for (open, close) in pairs where value.first == open && value.last == close && value.count > 1 {
            value = String(value.dropFirst().dropLast()).trimmingCharacters(in: .whitespacesAndNewlines)
        }
        return value
    }

    private static func clipToSentences(_ text: String, maxCharacters: Int) -> String {
        guard text.count > maxCharacters, maxCharacters > 1 else { return text }
        let limit = text.index(text.startIndex, offsetBy: maxCharacters)
        let prefix = text[..<limit]
        if let mark = prefix.lastIndex(where: { $0 == "." || $0 == "!" || $0 == "?" }) {
            return String(prefix[...mark]).trimmingCharacters(in: .whitespacesAndNewlines)
        }
        return String(prefix).trimmingCharacters(in: .whitespacesAndNewlines)
    }
}

/// Playhead math for skip, prefetch, and redirect cuts.
enum BlatherTimeline {
    /// How far Back and Forward move the playhead.
    static let skipStep: TimeInterval = 10
    /// Listening time to keep in reserve before the next model call.
    /// A 160-word passage is about a minute of speech, so 25 seconds at 1×
    /// leaves room to write and synthesize the next file. Faster playback
    /// multiplies this lead so the reserve stays about 25 seconds of waiting.
    static let prefetchLead: TimeInterval = 25
    /// Upper bound on passages written in one burst. Short clips chain until
    /// `prefetchLead` is satisfied; the cap stops a near-zero duration from
    /// looping.
    static let maxSegmentsPerFill = 4

    static func duration(of segments: [BlatherSegment]) -> TimeInterval {
        segments.reduce(0) { $0 + $1.duration }
    }

    static func clamped(_ time: TimeInterval, duration: TimeInterval) -> TimeInterval {
        min(max(0, time), max(0, duration))
    }

    static func skipped(_ time: TimeInterval, by delta: TimeInterval, duration: TimeInterval) -> TimeInterval {
        clamped(time + delta, duration: duration)
    }

    static func shouldPrefetch(
        playhead: TimeInterval,
        duration: TimeInterval,
        rate: Double = 1
    ) -> Bool {
        let playbackRate = min(max(rate, 0.5), 2)
        return duration - playhead <= prefetchLead * playbackRate
    }

    /// A time that lands on a boundary belongs to the following segment, except
    /// at the end of the timeline.
    static func locate(_ time: TimeInterval, durations: [TimeInterval]) -> (index: Int, offset: TimeInterval) {
        guard !durations.isEmpty else { return (0, 0) }
        var remaining = max(0, time)
        for (index, duration) in durations.enumerated() {
            let isLast = index == durations.count - 1
            if remaining < duration || isLast {
                let offset = min(max(0, remaining), max(0, duration))
                return (index, offset)
            }
            remaining -= duration
        }
        let last = max(0, durations[durations.count - 1])
        return (durations.count - 1, last)
    }

    /// Drops audio the listener has not heard and shortens the segment under
    /// the playhead so a new direction replaces the rest.
    static func cut(segments: [BlatherSegment], at time: TimeInterval) -> BlatherCut {
        var kept: [BlatherSegment] = []
        var removed: [String] = []
        var cursor: TimeInterval = 0
        let target = max(0, time)
        for segment in segments {
            let start = cursor
            let end = cursor + segment.duration
            if end <= target + 0.05 {
                kept.append(segment)
                cursor = end
                continue
            }
            if target <= start + 0.05 {
                removed.append(segment.fileName)
                cursor = end
                continue
            }
            var shortened = segment
            shortened.duration = target - start
            kept.append(shortened)
            cursor = target
        }
        let playhead = kept.reduce(0) { $0 + $1.duration }
        return BlatherCut(segments: kept, removedFileNames: removed, playhead: playhead)
    }
}

/// `m:ss` or `h:mm:ss` for the playhead readout.
enum BlatherClock {
    static func label(_ time: TimeInterval) -> String {
        let total = max(0, Int(time.rounded(.down)))
        let seconds = total % 60
        let minutes = (total / 60) % 60
        let hours = total / 3600
        if hours > 0 {
            return String(format: "%d:%02d:%02d", hours, minutes, seconds)
        }
        return String(format: "%d:%02d", total / 60, seconds)
    }
}
