import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Builds a short plain-language label for a finished ride using Apple's
/// on-device Foundation Models (`SystemLanguageModel`) when Apple Intelligence
/// is available. Returns `nil` when the model is unavailable or fails — no
/// heuristic substitute.
enum RideSummaryGenerator {
    /// Max characters kept for list rows (and after model cleanup).
    static let maxLength = 42

    /// Async entry point used when a ride finishes. `nil` means leave summary empty.
    static func summarize(for ride: Ride) async -> String? {
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            if let text = await foundationModelSummary(for: ride) {
                let cleaned = sanitize(text)
                return cleaned.isEmpty ? nil : cleaned
            }
        }
        #endif
        return nil
    }

    /// Compact stats block fed to the on-device model (no raw GPS track).
    static func factsPrompt(for ride: Ride) -> String {
        let minutes = ride.durationSeconds / 60
        let miles = RideUnits.miles(fromMeters: ride.distanceMeters)
        let hour = Calendar.current.component(.hour, from: ride.startedAt)
        var lines: [String] = [
            "Duration: \(String(format: "%.1f", minutes)) minutes",
            "Distance: \(String(format: "%.2f", miles)) miles",
            "Peak g: \(String(format: "%.1f", ride.peakG))",
            "Jolts: \(ride.joltCount)",
            "Possible crashes: \(ride.crashCount)",
            "Max speed: \(String(format: "%.1f", RideUnits.milesPerHour(fromMetersPerSecond: ride.maxSpeed))) mph",
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
        return text
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
