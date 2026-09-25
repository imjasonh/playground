import CoreGraphics
import Foundation

/// Target language for Live Translate overlays.
enum LiveTranslateLanguage: String, CaseIterable, Identifiable, Equatable {
    case english = "en"
    case spanish = "es"
    case french = "fr"
    case german = "de"
    case italian = "it"
    case portuguese = "pt"
    case japanese = "ja"
    case korean = "ko"
    case chineseSimplified = "zh-Hans"

    var id: String { rawValue }

    /// Localized language name for the current locale.
    var displayName: String {
        Locale.current.localizedString(forLanguageCode: rawValue) ?? rawValue
    }

    /// Short name used in prompts (English, so the model sees a stable token).
    var promptName: String {
        switch self {
        case .english: return "English"
        case .spanish: return "Spanish"
        case .french: return "French"
        case .german: return "German"
        case .italian: return "Italian"
        case .portuguese: return "Portuguese"
        case .japanese: return "Japanese"
        case .korean: return "Korean"
        case .chineseSimplified: return "Simplified Chinese"
        }
    }
}

/// One OCR line in Vision-normalized image space (origin bottom-left, 0…1).
struct LiveTranslateObservation: Equatable, Identifiable {
    let id: String
    let text: String
    let confidence: Double
    let boundingBox: CGRect

    init(
        id: String = UUID().uuidString,
        text: String,
        confidence: Double,
        boundingBox: CGRect
    ) {
        self.id = id
        self.text = text
        self.confidence = confidence
        self.boundingBox = boundingBox
    }
}

/// Sampled backdrop used to paint over the original glyphs.
struct LiveTranslateBackdrop: Equatable {
    let red: Double
    let green: Double
    let blue: Double
    let luma: Double

    static let neutral = LiveTranslateBackdrop(red: 0.96, green: 0.96, blue: 0.94, luma: 0.95)

    var usesDarkText: Bool {
        LiveTranslateColor.usesDarkText(luma: luma)
    }

    /// Moves `weight` of the way toward `sample`, so a line's fill doesn't flicker between passes.
    func blended(toward sample: LiveTranslateBackdrop, weight: Double) -> LiveTranslateBackdrop {
        let keep = 1 - weight
        return LiveTranslateBackdrop(
            red: red * keep + sample.red * weight,
            green: green * keep + sample.green * weight,
            blue: blue * keep + sample.blue * weight,
            luma: luma * keep + sample.luma * weight
        )
    }
}

/// Overlay drawn on top of one tracked line. `id` is the track id, so it stays the same across frames.
struct LiveTranslateOverlay: Equatable, Identifiable {
    let id: String
    let sourceText: String
    let displayText: String
    let boundingBox: CGRect
    let backdrop: LiveTranslateBackdrop
    let isTranslated: Bool
}

/// Last translation shown on a tracked line. It stays up while a changed
/// reading of that line waits for its own translation.
struct LiveTranslatePin: Equatable {
    let source: String
    let translation: String
    let language: LiveTranslateLanguage
}

/// Pure helpers for OCR ranking, overlays, translation batches, and clipboard text.
enum LiveTranslateResultBuilder {
    static let minimumConfidence = 0.35
    static let minimumBoxArea = 0.0015
    static let maximumObservations = 8
    static let maximumLineCharacters = 180
    /// Echo similarity that moves a model item to a different source line than its position.
    static let realignSimilarity = 0.8

    /// Filters, sorts into reading order (top-to-bottom, then left-to-right), and caps count.
    static func observations(
        from raw: [LiveTranslateObservation],
        minimumConfidence: Double = minimumConfidence,
        minimumBoxArea: Double = minimumBoxArea,
        maxCount: Int = maximumObservations
    ) -> [LiveTranslateObservation] {
        let kept = raw.filter { observation in
            let text = normalize(observation.text)
            let area = observation.boundingBox.width * observation.boundingBox.height
            return !text.isEmpty
                && observation.confidence >= minimumConfidence
                && area >= minimumBoxArea
        }
        .sorted { readsBefore($0.boundingBox, $1.boundingBox) }
        return Array(kept.prefix(max(0, maxCount)))
    }

    /// Reading order for Vision boxes: top line first, then left to right within a line.
    static func readsBefore(_ lhs: CGRect, _ rhs: CGRect) -> Bool {
        if abs(lhs.maxY - rhs.maxY) > 0.02 {
            return lhs.maxY > rhs.maxY
        }
        return lhs.minX < rhs.minX
    }

    static func normalize(_ text: String) -> String {
        text
            .replacingOccurrences(of: #"\s+"#, with: " ", options: .regularExpression)
            .trimmingCharacters(in: .whitespacesAndNewlines)
    }

    static func clip(_ text: String, maxCharacters: Int = maximumLineCharacters) -> String {
        guard text.count > maxCharacters else { return text }
        return String(text.prefix(maxCharacters)).trimmingCharacters(in: .whitespaces)
    }

    /// Overlays for tracked lines.
    ///
    /// A line shows its stored translation when the memory has one. Otherwise it
    /// keeps the translation last shown on it (its pin) while a changed reading
    /// waits for a new one. Untranslated lines appear only once settled, so a
    /// one-pass misread never flashes a box. A line missed this pass hides
    /// under a line read this pass that covers it. `pins` is updated in place
    /// and pruned to the lines still tracked.
    static func overlays(
        tracks: [LiveTranslateTrack],
        memory: LiveTranslateMemory,
        language: LiveTranslateLanguage,
        pins: inout [String: LiveTranslatePin],
        backdrops: [String: LiveTranslateBackdrop] = [:]
    ) -> [LiveTranslateOverlay] {
        var kept: [String: LiveTranslatePin] = [:]
        var shown: [(track: LiveTranslateTrack, translation: String?)] = []
        for track in tracks {
            var translation: String?
            if let stored = memory.translation(for: track.text, language: language) {
                translation = stored
                kept[track.id] = LiveTranslatePin(source: track.text, translation: stored, language: language)
            } else if let pin = pins[track.id],
                      pin.language == language,
                      LiveTranslateText.canKeepTranslation(of: pin.source, for: track.text)
            {
                translation = pin.translation
                kept[track.id] = pin
            }
            guard translation != nil || track.isSettled else { continue }
            shown.append((track, translation))
        }
        pins = kept

        let fresh = shown.filter { $0.track.misses == 0 }.map(\.track.boundingBox)
        return shown.compactMap { track, translation in
            if track.misses > 0, fresh.contains(where: { LiveTranslateTracker.covers(track.boundingBox, $0) }) {
                return nil
            }
            return LiveTranslateOverlay(
                id: track.id,
                sourceText: track.text,
                displayText: translation ?? track.text,
                boundingBox: track.boundingBox,
                backdrop: backdrops[track.id] ?? .neutral,
                isTranslated: translation != nil
            )
        }
    }

    /// Source text for the next model call: lines read this pass that settled
    /// and still lack a stored translation, in reading order, one per match key,
    /// skipping lines that failed recently.
    ///
    /// A line that failed before goes alone, so one line the model refuses
    /// can't keep failing the batch for every other line in view.
    static func translationBatch(
        tracks: [LiveTranslateTrack],
        memory: LiveTranslateMemory,
        language: LiveTranslateLanguage,
        now: Date,
        maxCount: Int = maximumObservations
    ) -> [String] {
        var keys: Set<String> = []
        var batch: [String] = []
        for track in tracks where track.isSettled && track.misses == 0 {
            guard batch.count < maxCount else { break }
            guard !keys.contains(track.key),
                  memory.translation(for: track.text, language: language) == nil,
                  !memory.isBlocked(source: track.text, language: language, at: now)
            else { continue }
            if memory.hasFailed(source: track.text, language: language) {
                if batch.isEmpty {
                    return [track.text]
                }
                continue
            }
            keys.insert(track.key)
            batch.append(track.text)
        }
        return batch
    }

    /// Translations the model has finished, keyed by index into `expected`.
    ///
    /// While a reply streams, its last item can still be growing, so an item
    /// counts as finished only once another item follows it, or when `isFinal`.
    /// An item pairs with the source at its position unless its echoed source
    /// clearly names a different line, which happens when the model skips or
    /// reorders lines.
    static func finishedTranslations(
        items: [(source: String?, translation: String?)],
        expected: [String],
        isFinal: Bool
    ) -> [Int: String] {
        let finished = isFinal ? items.count : max(0, items.count - 1)
        var result: [Int: String] = [:]
        for (position, item) in items.prefix(finished).enumerated() {
            let translation = clip(normalize(item.translation ?? ""))
            guard !translation.isEmpty,
                  let index = alignedIndex(
                    reported: item.source,
                    position: position,
                    expected: expected,
                    taken: Set(result.keys)
                  )
            else { continue }
            result[index] = translation
        }
        return result
    }

    static func alignedIndex(
        reported: String?,
        position: Int,
        expected: [String],
        taken: Set<Int>
    ) -> Int? {
        let reportedKey = LiveTranslateText.matchKey(reported ?? "")
        func echoSimilarity(_ index: Int) -> Double {
            guard !reportedKey.isEmpty else { return 0 }
            return LiveTranslateText.similarity(reportedKey, LiveTranslateText.matchKey(expected[index]))
        }
        let positional = expected.indices.contains(position) && !taken.contains(position) ? position : nil
        var best = positional
        var bestSimilarity = positional.map(echoSimilarity) ?? 0
        for index in expected.indices where index != positional && !taken.contains(index) {
            let similarity = echoSimilarity(index)
            if similarity >= realignSimilarity, similarity > bestSimilarity {
                best = index
                bestSimilarity = similarity
            }
        }
        return best
    }

    static func clipboardPayload(from overlays: [LiveTranslateOverlay]) -> String {
        overlays
            .map { $0.isTranslated ? $0.displayText : $0.sourceText }
            .map { normalize($0) }
            .filter { !$0.isEmpty }
            .joined(separator: "\n")
    }

    /// Copies again only when the payload has a line the last copy didn't.
    ///
    /// Lines leave and reenter the frame as the camera moves. A line coming
    /// back must not rewrite the pasteboard or fire another haptic.
    static func shouldCopy(newPayload: String, lastCopied: String?) -> Bool {
        let lines = payloadLines(newPayload)
        guard !lines.isEmpty else { return false }
        return !lines.isSubset(of: payloadLines(lastCopied ?? ""))
    }

    private static func payloadLines(_ payload: String) -> Set<String> {
        Set(
            payload
                .split(separator: "\n")
                .map { normalize(String($0)) }
                .filter { !$0.isEmpty }
        )
    }

    static func fittedFontSize(
        text: String,
        box: CGSize,
        minimum: CGFloat = 11,
        maximum: CGFloat = 36
    ) -> CGFloat {
        let width = max(box.width, 1)
        let height = max(box.height, 1)
        let characters = CGFloat(max(text.count, 1))
        let fromHeight = height * 0.62
        let fromWidth = width / max(characters * 0.62, 1)
        let size = min(fromHeight, fromWidth)
        return min(maximum, max(minimum, size))
    }
}

/// Relative-luminance helpers for overlay contrast.
enum LiveTranslateColor {
    static func luma(red: Double, green: Double, blue: Double) -> Double {
        (0.2126 * red) + (0.7152 * green) + (0.0722 * blue)
    }

    static func usesDarkText(luma: Double) -> Bool {
        luma > 0.55
    }

    /// Average color of `visionBox` in an upright image (Vision origin bottom-left).
    static func sample(image: CGImage, visionBox: CGRect) -> LiveTranslateBackdrop {
        let imageSize = CGSize(width: image.width, height: image.height)
        let rect = LocalLensCoordinateMapper.imageRect(
            fromVisionNormalized: visionBox,
            imageSize: imageSize
        )
        let bounds = CGRect(origin: .zero, size: imageSize)
        let clamped = rect.intersection(bounds).integral
        guard clamped.width >= 1, clamped.height >= 1 else {
            return .neutral
        }
        var pixel: [UInt8] = [0, 0, 0, 0]
        let colorSpace = CGColorSpaceCreateDeviceRGB()
        return pixel.withUnsafeMutableBytes { buffer in
            guard let base = buffer.baseAddress,
                  let context = CGContext(
                    data: base,
                    width: 1,
                    height: 1,
                    bitsPerComponent: 8,
                    bytesPerRow: 4,
                    space: colorSpace,
                    bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
                  )
            else {
                return .neutral
            }
            context.interpolationQuality = .medium
            guard let cropped = image.cropping(to: clamped) else {
                return .neutral
            }
            context.draw(cropped, in: CGRect(x: 0, y: 0, width: 1, height: 1))
            let red = Double(buffer[0]) / 255
            let green = Double(buffer[1]) / 255
            let blue = Double(buffer[2]) / 255
            return LiveTranslateBackdrop(
                red: red,
                green: green,
                blue: blue,
                luma: luma(red: red, green: green, blue: blue)
            )
        }
    }
}
