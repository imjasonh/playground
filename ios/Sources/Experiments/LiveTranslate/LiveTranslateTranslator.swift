import Foundation
import FoundationModels

/// Asks the on-device Foundation Model to translate a short list of OCR lines.
///
/// Each call starts a new `LanguageModelSession` so a live camera loop does not
/// accumulate transcript. A context-window overflow retries once with fewer lines.
enum LiveTranslateTranslator {
    static let maxItems = LiveTranslateResultBuilder.maximumObservations
    static let maxSourceCharacters = 180

    enum Failure: Error, Equatable, LocalizedError {
        case modelUnavailable
        case emptySources
        case modelFailed(String)

        var errorDescription: String? {
            switch self {
            case .modelUnavailable:
                return "Apple Intelligence isn't available."
            case .emptySources:
                return "No text to translate."
            case .modelFailed(let message):
                return message
            }
        }
    }

    static func instructions(language: LiveTranslateLanguage) -> String {
        """
        Translate each OCR line into \(language.promptName).
        Keep the same count and order.
        Copy numbers, names, and URLs unchanged.
        Do not add quotes or commentary.
        """
    }

    static func preparedSources(_ observations: [LiveTranslateObservation]) -> [String] {
        observations
            .map { clip(LiveTranslateResultBuilder.normalize($0.text)) }
            .filter { !$0.isEmpty }
            .prefix(maxItems)
            .map { $0 }
    }

    static func retrySources(_ sources: [String]) -> [String] {
        Array(sources.prefix(max(1, sources.count / 2)))
    }

    static func prompt(sources: [String], language: LiveTranslateLanguage) -> String {
        var lines = [
            "Translate each numbered line into \(language.promptName).",
            "Return one item per line, same order, with the original source text.",
        ]
        for (index, source) in sources.enumerated() {
            lines.append("\(index + 1). \(source)")
        }
        return lines.joined(separator: "\n")
    }

    static func translate(
        observations: [LiveTranslateObservation],
        language: LiveTranslateLanguage
    ) async throws -> [LiveTranslateItem] {
        let model = SystemLanguageModel.default
        guard model.isAvailable else {
            throw Failure.modelUnavailable
        }
        let sources = preparedSources(observations)
        guard !sources.isEmpty else {
            throw Failure.emptySources
        }
        do {
            return try await run(sources: sources, language: language)
        } catch {
            guard OnDeviceContextManager.isExceededContextWindow(error), sources.count > 1 else {
                throw mapped(error)
            }
            do {
                return try await run(sources: retrySources(sources), language: language)
            } catch {
                throw mapped(error)
            }
        }
    }

    private static func run(
        sources: [String],
        language: LiveTranslateLanguage
    ) async throws -> [LiveTranslateItem] {
        let session = LanguageModelSession(instructions: instructions(language: language))
        session.prewarm()
        let response = try await session.respond(
            to: prompt(sources: sources, language: language),
            generating: Batch.self
        )
        return sanitize(
            pairs: response.content.items.map { ($0.source, $0.translation) },
            expected: sources
        )
    }

    static func sanitize(
        pairs: [(source: String, translation: String)],
        expected: [String]
    ) -> [LiveTranslateItem] {
        let capped = pairs.prefix(maxItems)
        return zip(expected, capped).compactMap { source, pair in
            let translation = LiveTranslateResultBuilder.normalize(pair.translation)
            guard !translation.isEmpty else { return nil }
            let reported = LiveTranslateResultBuilder.normalize(pair.source)
            return LiveTranslateItem(
                source: reported.isEmpty ? source : reported,
                translation: clip(translation)
            )
        }
    }

    private static func clip(_ raw: String) -> String {
        if raw.count <= maxSourceCharacters {
            return raw
        }
        let end = raw.index(raw.startIndex, offsetBy: maxSourceCharacters)
        return String(raw[..<end]).trimmingCharacters(in: .whitespaces)
    }

    private static func mapped(_ error: Error) -> Error {
        if let failure = error as? Failure {
            return failure
        }
        return Failure.modelFailed(error.localizedDescription)
    }

    @Generable
    struct Batch {
        @Guide(.maximumCount(8))
        @Guide(description: "One translation per OCR line, same order")
        var items: [Item]
    }

    @Generable
    struct Item {
        var source: String
        var translation: String
    }
}
