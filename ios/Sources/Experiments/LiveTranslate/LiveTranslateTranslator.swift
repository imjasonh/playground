import Foundation
import FoundationModels

/// Asks the on-device Foundation Model to translate a short list of OCR lines.
///
/// Each call starts a new `LanguageModelSession` so a live camera loop does not
/// accumulate transcript. The reply streams, and each line is reported as soon
/// as the model finishes it. A context-window overflow retries once with fewer
/// lines.
enum LiveTranslateTranslator {
    static let maxItems = LiveTranslateResultBuilder.maximumObservations
    static let maxSourceCharacters = LiveTranslateResultBuilder.maximumLineCharacters

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

    /// Prompt lines for `sources`: normalized, clipped, and capped. Index `i`
    /// here is index `i` in `sources`.
    static func promptLines(_ sources: [String]) -> [String] {
        sources
            .prefix(maxItems)
            .map { LiveTranslateResultBuilder.clip(LiveTranslateResultBuilder.normalize($0)) }
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

    /// Starts loading the model so the first batch doesn't wait for it.
    static func prewarm(language: LiveTranslateLanguage) {
        guard SystemLanguageModel.default.isAvailable else { return }
        LanguageModelSession(instructions: instructions(language: language)).prewarm()
    }

    /// Translates `sources` and returns translations keyed by index into `sources`.
    ///
    /// `onProgress` receives each line's translation as soon as the model
    /// finishes it, before the rest of the batch. Lines the model skipped are
    /// missing from the result.
    static func translate(
        sources: [String],
        language: LiveTranslateLanguage,
        onProgress: @escaping @MainActor ([Int: String]) -> Void
    ) async throws -> [Int: String] {
        guard SystemLanguageModel.default.isAvailable else {
            throw Failure.modelUnavailable
        }
        let lines = promptLines(sources)
        guard lines.contains(where: { !$0.isEmpty }) else {
            throw Failure.emptySources
        }
        do {
            return try await run(lines: lines, language: language, onProgress: onProgress)
        } catch {
            guard OnDeviceContextManager.isExceededContextWindow(error), lines.count > 1 else {
                throw mapped(error)
            }
            do {
                return try await run(lines: retrySources(lines), language: language, onProgress: onProgress)
            } catch {
                throw mapped(error)
            }
        }
    }

    private static func run(
        lines: [String],
        language: LiveTranslateLanguage,
        onProgress: @escaping @MainActor ([Int: String]) -> Void
    ) async throws -> [Int: String] {
        let session = LanguageModelSession(instructions: instructions(language: language))
        let stream = session.streamResponse(
            to: prompt(sources: lines, language: language),
            generating: Batch.self
        )
        var latest: [(source: String?, translation: String?)] = []
        var reported: [Int: String] = [:]
        for try await snapshot in stream {
            latest = (snapshot.content.items ?? []).map { item in
                (source: item.source, translation: item.translation)
            }
            let fresh = LiveTranslateResultBuilder
                .finishedTranslations(items: latest, expected: lines, isFinal: false)
                .filter { reported[$0.key] == nil }
            guard !fresh.isEmpty else { continue }
            reported.merge(fresh) { current, _ in current }
            await onProgress(fresh)
        }
        withExtendedLifetime(session) {}
        return LiveTranslateResultBuilder.finishedTranslations(items: latest, expected: lines, isFinal: true)
    }

    private static func mapped(_ error: Error) -> Error {
        if error is CancellationError {
            return error
        }
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
