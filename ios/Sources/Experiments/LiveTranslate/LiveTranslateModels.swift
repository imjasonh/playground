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
}

/// Overlay drawn on top of one OCR box.
struct LiveTranslateOverlay: Equatable, Identifiable {
    let id: String
    let sourceText: String
    let displayText: String
    let boundingBox: CGRect
    let backdrop: LiveTranslateBackdrop
    let isTranslated: Bool
}

/// One model translation keyed to a source line.
struct LiveTranslateItem: Equatable {
    let source: String
    let translation: String
}

/// Pure helpers for OCR ranking, fingerprints, pairing, and clipboard text.
enum LiveTranslateResultBuilder {
    static let minimumConfidence = 0.35
    static let minimumBoxArea = 0.0015
    static let maximumObservations = 8
    static let holdInterval: TimeInterval = 0.4

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
        .sorted { lhs, rhs in
            let ly = lhs.boundingBox.maxY
            let ry = rhs.boundingBox.maxY
            if abs(ly - ry) > 0.02 {
                return ly > ry
            }
            return lhs.boundingBox.minX < rhs.boundingBox.minX
        }
        return Array(kept.prefix(max(0, maxCount)))
    }

    static func normalize(_ text: String) -> String {
        text
            .replacingOccurrences(of: #"\s+"#, with: " ", options: .regularExpression)
            .trimmingCharacters(in: .whitespacesAndNewlines)
    }

    /// Stable key for a set of OCR lines. Order is ignored so a reshuffle does not retrigger.
    static func fingerprint(for observations: [LiveTranslateObservation]) -> String {
        observations
            .map { normalize($0.text) }
            .filter { !$0.isEmpty }
            .sorted()
            .joined(separator: "\n")
    }

    /// Hold the same fingerprint for `holdInterval` before spending a model call.
    static func shouldTranslate(
        current: String,
        pending: String?,
        pendingSince: Date?,
        now: Date,
        holdInterval: TimeInterval = holdInterval
    ) -> Bool {
        guard !current.isEmpty, current == pending, let pendingSince else {
            return false
        }
        return now.timeIntervalSince(pendingSince) >= holdInterval
    }

    /// Pair live boxes with the latest model items. Exact source match first, then leftover order.
    static func overlays(
        observations: [LiveTranslateObservation],
        items: [LiveTranslateItem],
        backdrops: [String: LiveTranslateBackdrop] = [:]
    ) -> [LiveTranslateOverlay] {
        var remaining = items.filter { !normalize($0.translation).isEmpty }
        return observations.map { observation in
            let key = normalize(observation.text)
            let translation: String?
            if let index = remaining.firstIndex(where: { normalize($0.source) == key }) {
                translation = remaining.remove(at: index).translation
            } else if !remaining.isEmpty {
                translation = remaining.removeFirst().translation
            } else {
                translation = nil
            }
            let display = normalize(translation ?? "")
            let isTranslated = !display.isEmpty
            return LiveTranslateOverlay(
                id: observation.id,
                sourceText: observation.text,
                displayText: isTranslated ? display : observation.text,
                boundingBox: observation.boundingBox,
                backdrop: backdrops[observation.id] ?? .neutral,
                isTranslated: isTranslated
            )
        }
    }

    static func clipboardPayload(from overlays: [LiveTranslateOverlay]) -> String {
        overlays
            .map { $0.isTranslated ? $0.displayText : $0.sourceText }
            .map { normalize($0) }
            .filter { !$0.isEmpty }
            .joined(separator: "\n")
    }

    static func shouldCopy(newPayload: String, lastCopied: String?) -> Bool {
        let trimmed = normalize(newPayload)
        guard !trimmed.isEmpty else { return false }
        return trimmed != lastCopied
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
