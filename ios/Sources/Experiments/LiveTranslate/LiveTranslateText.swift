import Foundation

/// Keys and similarity scores for comparing noisy OCR readings of the same line.
enum LiveTranslateText {
    /// Similarity a pinned translation needs to stay on a line whose reading changed.
    static let keepTranslationSimilarity = 0.5

    /// Case-, accent-, width-, spacing-, and punctuation-insensitive form of `text`.
    ///
    /// Text with no letters or digits keys on its normalized form instead, so
    /// symbol-only lines still get a stable key.
    static func matchKey(_ text: String) -> String {
        let folded = text.folding(
            options: [.caseInsensitive, .diacriticInsensitive, .widthInsensitive],
            locale: nil
        )
        var kept = String.UnicodeScalarView()
        for scalar in folded.unicodeScalars where CharacterSet.alphanumerics.contains(scalar) {
            kept.append(scalar)
        }
        if kept.isEmpty {
            return LiveTranslateResultBuilder.normalize(folded)
        }
        return String(kept)
    }

    /// Decimal digits in `key`, in order. Prices, table numbers, and times must
    /// match exactly before two readings share a translation.
    static func digits(_ key: String) -> String {
        var kept = String.UnicodeScalarView()
        for scalar in key.unicodeScalars where CharacterSet.decimalDigits.contains(scalar) {
            kept.append(scalar)
        }
        return String(kept)
    }

    /// 1 minus the edit distance over the longer length: 1 for equal strings, 0 for nothing in common.
    static func similarity(_ lhs: String, _ rhs: String) -> Double {
        let left = Array(lhs.unicodeScalars)
        let right = Array(rhs.unicodeScalars)
        let longest = max(left.count, right.count)
        guard longest > 0 else { return 1 }
        return 1 - Double(editDistance(left, right)) / Double(longest)
    }

    /// Levenshtein distance over Unicode scalars.
    static func editDistance(_ lhs: [Unicode.Scalar], _ rhs: [Unicode.Scalar]) -> Int {
        guard !lhs.isEmpty else { return rhs.count }
        guard !rhs.isEmpty else { return lhs.count }
        var previous = Array(0...rhs.count)
        var current = [Int](repeating: 0, count: rhs.count + 1)
        for row in 1...lhs.count {
            current[0] = row
            for column in 1...rhs.count {
                let substitution = previous[column - 1] + (lhs[row - 1] == rhs[column - 1] ? 0 : 1)
                current[column] = min(previous[column] + 1, current[column - 1] + 1, substitution)
            }
            swap(&previous, &current)
        }
        return previous[rhs.count]
    }

    /// Whether a translation made for `pinned` can stay on screen while the
    /// line reads `current` and its own translation is pending.
    static func canKeepTranslation(of pinned: String, for current: String) -> Bool {
        let pinnedKey = matchKey(pinned)
        let currentKey = matchKey(current)
        guard digits(pinnedKey) == digits(currentKey) else { return false }
        return similarity(pinnedKey, currentKey) >= keepTranslationSimilarity
    }
}
