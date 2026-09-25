import Foundation

/// Translations the model already produced, stored per target language by source text.
///
/// The camera shows the same line in many frames. After the model translates a
/// line once, every later frame that reads that text reuses the stored
/// translation. A reading that differs only by case, accents, spacing, or
/// punctuation matches exactly. A reading a letter or two off also matches when
/// its digits are identical. The memory also records lines the model failed to
/// translate so the live loop backs off instead of asking again every pass.
struct LiveTranslateMemory {
    /// Entries kept per language. The oldest entry goes first.
    static let capacity = 256
    /// Similarity a new reading needs to reuse a stored translation that isn't an exact key match.
    static let nearMatchSimilarity = 0.85
    /// Wait after the first failure. Each later failure doubles it.
    static let firstRetryDelay: TimeInterval = 2
    static let maximumRetryDelay: TimeInterval = 30

    private struct Entry {
        let key: String
        let digits: String
        let length: Int
        let translation: String
        let order: Int
    }

    private struct Failure {
        var attempts: Int
        var retryAt: Date
    }

    private var entries: [LiveTranslateLanguage: [String: Entry]] = [:]
    private var failures: [LiveTranslateLanguage: [String: Failure]] = [:]
    private var insertions = 0

    func count(for language: LiveTranslateLanguage) -> Int {
        entries[language]?.count ?? 0
    }

    mutating func remember(source: String, translation: String, language: LiveTranslateLanguage) {
        let key = LiveTranslateText.matchKey(source)
        let clean = LiveTranslateResultBuilder.normalize(translation)
        guard !key.isEmpty, !clean.isEmpty else { return }
        failures[language]?.removeValue(forKey: key)
        var table = entries[language] ?? [:]
        if table[key]?.translation == clean {
            return
        }
        insertions += 1
        table[key] = Entry(
            key: key,
            digits: LiveTranslateText.digits(key),
            length: key.unicodeScalars.count,
            translation: clean,
            order: insertions
        )
        if table.count > Self.capacity,
           let oldest = table.values.min(by: { $0.order < $1.order })
        {
            table.removeValue(forKey: oldest.key)
        }
        entries[language] = table
    }

    /// Stored translation for `source`: an exact key match first, then the
    /// closest near match with the same digits.
    func translation(for source: String, language: LiveTranslateLanguage) -> String? {
        let key = LiveTranslateText.matchKey(source)
        guard !key.isEmpty, let table = entries[language] else { return nil }
        if let exact = table[key] {
            return exact.translation
        }
        let digits = LiveTranslateText.digits(key)
        let length = key.unicodeScalars.count
        let slack = 1 - Self.nearMatchSimilarity
        var best: (similarity: Double, entry: Entry)?
        for entry in table.values where entry.digits == digits {
            // Edit distance is at least the length gap, so skip entries that can't reach the threshold.
            let gap = Double(abs(entry.length - length))
            guard gap <= slack * Double(max(entry.length, length)) else { continue }
            let similarity = LiveTranslateText.similarity(key, entry.key)
            guard similarity >= Self.nearMatchSimilarity else { continue }
            if let current = best, (current.similarity, current.entry.order) >= (similarity, entry.order) {
                continue
            }
            best = (similarity, entry)
        }
        return best?.entry.translation
    }

    /// Notes that the model returned nothing usable for `source`, and delays the next try.
    mutating func recordFailure(source: String, language: LiveTranslateLanguage, at now: Date) {
        let key = LiveTranslateText.matchKey(source)
        guard !key.isEmpty else { return }
        let attempts = (failures[language]?[key]?.attempts ?? 0) + 1
        let delay = min(
            Self.maximumRetryDelay,
            Self.firstRetryDelay * pow(2, Double(attempts - 1))
        )
        failures[language, default: [:]][key] = Failure(
            attempts: attempts,
            retryAt: now.addingTimeInterval(delay)
        )
    }

    /// Whether `source` failed since it was last translated.
    func hasFailed(source: String, language: LiveTranslateLanguage) -> Bool {
        failures[language]?[LiveTranslateText.matchKey(source)] != nil
    }

    /// Whether `source` failed recently enough that the live loop skips it for now.
    func isBlocked(source: String, language: LiveTranslateLanguage, at now: Date) -> Bool {
        let key = LiveTranslateText.matchKey(source)
        guard let failure = failures[language]?[key] else { return false }
        return now < failure.retryAt
    }
}
