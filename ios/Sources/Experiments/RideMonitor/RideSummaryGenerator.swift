import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Builds a short plain-language label for a finished ride.
///
/// Prefers Apple's on-device Foundation Models (`SystemLanguageModel`) when
/// Apple Intelligence is available; otherwise falls back to a deterministic
/// heuristic so every ride still gets a list caption on older devices / OS.
enum RideSummaryGenerator {
    /// Max characters kept for list rows (and after model cleanup).
    static let maxLength = 42

    /// Async entry point used when a ride finishes.
    static func summarize(for ride: Ride) async -> String {
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            if let text = await foundationModelSummary(for: ride) {
                return sanitize(text)
            }
        }
        #endif
        return heuristicSummary(for: ride)
    }

    /// Deterministic few-word label from ride stats (always available; unit-tested).
    static func heuristicSummary(for ride: Ride) -> String {
        let minutes = Int(ride.durationSeconds / 60)
        let km = ride.distanceMeters / 1000
        let joltsPerMin = ride.durationSeconds > 0
            ? Double(ride.joltCount) / (ride.durationSeconds / 60)
            : Double(ride.joltCount)

        if ride.crashCount > 0 {
            return sanitize(ride.crashCount == 1 ? "Hard stop, possible crash" : "Rough ride, crash alerts")
        }
        if ride.peakG >= 4.0 {
            return sanitize("Hard impacts, peak \(formatG(ride.peakG))")
        }
        if joltsPerMin >= 4 || ride.joltCount >= 40 {
            return sanitize("Very bumpy \(distancePhrase(km: km, minutes: minutes))")
        }
        if joltsPerMin >= 1.5 || ride.joltCount >= 12 {
            return sanitize("Bumpy \(distancePhrase(km: km, minutes: minutes))")
        }
        if let gain = ride.elevationGain, abs(gain) >= 25 {
            if gain >= 25 {
                return sanitize("Climbing \(distancePhrase(km: km, minutes: minutes))")
            }
            return sanitize("Downhill \(distancePhrase(km: km, minutes: minutes))")
        }
        if km < 0.3 && minutes < 3 {
            return sanitize("Short smooth hop")
        }
        if joltsPerMin < 0.4 && ride.joltCount < 5 {
            return sanitize("Smooth \(distancePhrase(km: km, minutes: minutes))")
        }
        return sanitize("Steady \(distancePhrase(km: km, minutes: minutes))")
    }

    /// Compact stats block fed to the on-device model (no raw GPS track).
    static func factsPrompt(for ride: Ride) -> String {
        let minutes = ride.durationSeconds / 60
        let km = ride.distanceMeters / 1000
        let hour = Calendar.current.component(.hour, from: ride.startedAt)
        var lines: [String] = [
            "Duration: \(String(format: "%.1f", minutes)) minutes",
            "Distance: \(String(format: "%.2f", km)) km",
            "Peak g: \(String(format: "%.1f", ride.peakG))",
            "Jolts: \(ride.joltCount)",
            "Possible crashes: \(ride.crashCount)",
            "Max speed: \(String(format: "%.1f", ride.maxSpeed * 3.6)) km/h",
            "Started hour (local): \(hour)",
        ]
        if let gain = ride.elevationGain {
            lines.append("Net elevation: \(String(format: "%+.0f", gain)) m")
        }
        let severities = Dictionary(grouping: ride.events, by: \.severity)
            .map { "\($0.key.rawValue)=\($0.value.count)" }
            .sorted()
            .joined(separator: ", ")
        if !severities.isEmpty {
            lines.append("Events: \(severities)")
        }
        return lines.joined(separator: "\n")
    }

    static func sanitize(_ raw: String) -> String {
        var text = raw
            .replacingOccurrences(of: "\"", with: "")
            .replacingOccurrences(of: "“", with: "")
            .replacingOccurrences(of: "”", with: "")
            .trimmingCharacters(in: .whitespacesAndNewlines)
        if let firstLine = text.split(whereSeparator: \.isNewline).first {
            text = String(firstLine).trimmingCharacters(in: .whitespacesAndNewlines)
        }
        while text.hasSuffix(".") || text.hasSuffix("!") || text.hasSuffix("?") {
            text = String(text.dropLast()).trimmingCharacters(in: .whitespaces)
        }
        if text.count > maxLength {
            let end = text.index(text.startIndex, offsetBy: maxLength)
            text = String(text[..<end]).trimmingCharacters(in: .whitespaces)
            if let lastSpace = text.lastIndex(of: " "), lastSpace > text.startIndex {
                text = String(text[..<lastSpace])
            }
        }
        return text.isEmpty ? "Ride" : text
    }

    private static func distancePhrase(km: Double, minutes: Int) -> String {
        if km < 0.5 {
            return minutes <= 5 ? "short ride" : "slow ride"
        }
        if km < 3 {
            return "short ride"
        }
        if km < 10 {
            return "ride"
        }
        return "long ride"
    }

    private static func formatG(_ g: Double) -> String {
        String(format: "%.1fg", g)
    }

    #if canImport(FoundationModels)
    @available(iOS 26.0, *)
    private static func foundationModelSummary(for ride: Ride) async -> String? {
        let model = SystemLanguageModel.default
        guard model.isAvailable else { return nil }

        let session = LanguageModelSession(instructions: """
            You label finished bike or scooter rides for a short list row.
            Reply with a plain English phrase of 3 to 6 words only.
            No quotes, no emoji, no punctuation at the end, no preamble.
            Reflect roughness, crashes, distance, or calmness from the stats.
            """)
        let prompt = """
            Write a 3–6 word label for this ride:
            \(factsPrompt(for: ride))
            """
        do {
            let response = try await session.respond(to: prompt)
            let content = response.content.trimmingCharacters(in: .whitespacesAndNewlines)
            return content.isEmpty ? nil : content
        } catch {
            return nil
        }
    }
    #endif
}
