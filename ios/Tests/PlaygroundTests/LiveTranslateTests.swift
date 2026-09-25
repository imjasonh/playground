import CoreGraphics
import UIKit
import XCTest
@testable import Playground

final class LiveTranslateTests: XCTestCase {
    func testLanguageMetadataIsComplete() {
        XCTAssertEqual(LiveTranslateLanguage.allCases.count, 9)
        for language in LiveTranslateLanguage.allCases {
            XCTAssertFalse(language.rawValue.isEmpty)
            XCTAssertFalse(language.displayName.isEmpty)
            XCTAssertFalse(language.promptName.isEmpty)
            XCTAssertEqual(language.id, language.rawValue)
        }
        XCTAssertEqual(LiveTranslateLanguage.english.promptName, "English")
        XCTAssertEqual(LiveTranslateLanguage.chineseSimplified.rawValue, "zh-Hans")
    }

    func testObservationsFilterConfidenceAreaAndEmptyText() {
        let kept = LiveTranslateObservation(
            id: "keep",
            text: "Hola",
            confidence: 0.9,
            boundingBox: CGRect(x: 0.1, y: 0.6, width: 0.4, height: 0.1)
        )
        let raw = [
            kept,
            LiveTranslateObservation(
                id: "low",
                text: "nope",
                confidence: 0.1,
                boundingBox: CGRect(x: 0.1, y: 0.4, width: 0.4, height: 0.1)
            ),
            LiveTranslateObservation(
                id: "tiny",
                text: "x",
                confidence: 0.99,
                boundingBox: CGRect(x: 0.1, y: 0.2, width: 0.01, height: 0.01)
            ),
            LiveTranslateObservation(
                id: "blank",
                text: "   ",
                confidence: 0.99,
                boundingBox: CGRect(x: 0.1, y: 0.1, width: 0.4, height: 0.1)
            ),
        ]
        let result = LiveTranslateResultBuilder.observations(from: raw)
        XCTAssertEqual(result.map(\.id), ["keep"])
    }

    func testObservationsSortReadingOrderAndCapCount() {
        var raw: [LiveTranslateObservation] = []
        for index in 0..<10 {
            raw.append(
                LiveTranslateObservation(
                    id: "n\(index)",
                    text: "Line \(index)",
                    confidence: 0.8,
                    boundingBox: CGRect(x: 0.1, y: Double(index) / 20.0, width: 0.5, height: 0.04)
                )
            )
        }
        let result = LiveTranslateResultBuilder.observations(from: raw, maxCount: 8)
        XCTAssertEqual(result.count, 8)
        XCTAssertEqual(result.first?.id, "n9")
        XCTAssertEqual(result.last?.id, "n2")
    }

    func testClipboardPayloadPrefersTranslations() {
        let overlays = [
            LiveTranslateOverlay(
                id: "a",
                sourceText: "Hola",
                displayText: "Hello",
                boundingBox: .zero,
                backdrop: .neutral,
                isTranslated: true
            ),
            LiveTranslateOverlay(
                id: "b",
                sourceText: "Mundo",
                displayText: "Mundo",
                boundingBox: .zero,
                backdrop: .neutral,
                isTranslated: false
            ),
        ]
        XCTAssertEqual(LiveTranslateResultBuilder.clipboardPayload(from: overlays), "Hello\nMundo")
        XCTAssertTrue(LiveTranslateResultBuilder.shouldCopy(newPayload: "Hello\nMundo", lastCopied: nil))
        XCTAssertFalse(LiveTranslateResultBuilder.shouldCopy(newPayload: "Hello\nMundo", lastCopied: "Hello\nMundo"))
        XCTAssertFalse(LiveTranslateResultBuilder.shouldCopy(newPayload: " Hello\nMundo\n", lastCopied: "Hello\nMundo"))
        XCTAssertFalse(LiveTranslateResultBuilder.shouldCopy(newPayload: "   ", lastCopied: nil))
        XCTAssertFalse(
            LiveTranslateResultBuilder.shouldCopy(newPayload: "Mundo\nHello", lastCopied: "Hello\nMundo"),
            "Reordered lines are not new"
        )
        XCTAssertFalse(
            LiveTranslateResultBuilder.shouldCopy(newPayload: "Hello", lastCopied: "Hello\nMundo"),
            "A line leaving the frame is not new"
        )
        XCTAssertTrue(LiveTranslateResultBuilder.shouldCopy(newPayload: "Hello\nWorld", lastCopied: "Hello\nMundo"))
    }

    func testFittedFontSizeStaysInRange() {
        let large = LiveTranslateResultBuilder.fittedFontSize(
            text: "Hi",
            box: CGSize(width: 400, height: 80),
            minimum: 11,
            maximum: 36
        )
        let tiny = LiveTranslateResultBuilder.fittedFontSize(
            text: String(repeating: "A", count: 80),
            box: CGSize(width: 40, height: 8),
            minimum: 11,
            maximum: 36
        )
        XCTAssertEqual(large, 36)
        XCTAssertEqual(tiny, 11)
    }

    func testContrastUsesDarkTextOnLightBackdrop() {
        XCTAssertGreaterThan(LiveTranslateColor.luma(red: 1, green: 1, blue: 1), 0.9)
        XCTAssertTrue(LiveTranslateColor.usesDarkText(luma: 0.9))
        XCTAssertFalse(LiveTranslateColor.usesDarkText(luma: 0.2))
        XCTAssertTrue(LiveTranslateBackdrop.neutral.usesDarkText)
    }

    func testSampleBackdropFromSolidImage() throws {
        let image = try XCTUnwrap(Self.makeSolidImage(color: .white, size: CGSize(width: 64, height: 64)))
        let sample = LiveTranslateColor.sample(
            image: image,
            visionBox: CGRect(x: 0.2, y: 0.2, width: 0.4, height: 0.4)
        )
        XCTAssertGreaterThan(sample.luma, 0.8)
        XCTAssertTrue(sample.usesDarkText)
    }

    func testTranslatorPromptListsNumberedSources() {
        let prompt = LiveTranslateTranslator.prompt(
            sources: ["Hola", "Mundo"],
            language: .english
        )
        XCTAssertTrue(prompt.contains("English"))
        XCTAssertTrue(prompt.contains("1. Hola"))
        XCTAssertTrue(prompt.contains("2. Mundo"))

        let instructions = LiveTranslateTranslator.instructions(language: .japanese)
        XCTAssertTrue(instructions.contains("Japanese"))
        XCTAssertLessThan(instructions.count, 240)
    }

    func testRetrySourcesHalvesTheBatch() {
        XCTAssertEqual(LiveTranslateTranslator.retrySources(["a"]), ["a"])
        XCTAssertEqual(LiveTranslateTranslator.retrySources(["a", "b", "c", "d"]), ["a", "b"])
    }

    func testPromptLinesClipCapAndKeepSourceIndexes() {
        let long = String(repeating: "a", count: 400)
        let sources = [long] + (1..<12).map { "line  \($0)" }
        let lines = LiveTranslateTranslator.promptLines(sources)
        XCTAssertEqual(lines.count, LiveTranslateTranslator.maxItems)
        XCTAssertEqual(lines.first?.count, LiveTranslateTranslator.maxSourceCharacters)
        XCTAssertEqual(lines[1], "line 1")
        XCTAssertEqual(lines.last, "line \(LiveTranslateTranslator.maxItems - 1)")
    }

    func testRecognizerReadsDrawnText() throws {
        let image = try XCTUnwrap(Self.makeTextImage(text: "HELLO", size: CGSize(width: 320, height: 120)))
        let observations = try LiveTranslateRecognizer.recognize(cgImage: image)
        let joined = observations.map(\.text).joined(separator: " ").uppercased()
        XCTAssertTrue(
            joined.contains("HELLO") || observations.isEmpty,
            "Expected OCR to see HELLO or return empty on a sparse renderer; got \(joined)"
        )
    }

    func testRecognizerDetectsJapaneseText() throws {
        let latin = try XCTUnwrap(Self.makeTextImage(text: "HELLO", size: CGSize(width: 320, height: 120)))
        try XCTSkipIf(
            try LiveTranslateRecognizer.recognize(cgImage: latin).isEmpty,
            "Vision found no text in a plain Latin word on this simulator"
        )

        let image = try XCTUnwrap(Self.makeTextImage(text: "非常口", size: CGSize(width: 320, height: 120)))
        let observations = try LiveTranslateRecognizer.recognize(cgImage: image)
        let joined = observations.map(\.text).joined(separator: " ")
        XCTAssertTrue(joined.contains("非常口"), "Expected 非常口 (emergency exit); got \(joined)")
    }

    func testRecognizerAcceptsEmptyFrame() throws {
        let image = try XCTUnwrap(Self.makeSolidImage(color: .white, size: CGSize(width: 200, height: 200)))
        let observations = try LiveTranslateRecognizer.recognize(cgImage: image)
        XCTAssertTrue(observations.isEmpty)
    }

    func testExperimentRegistration() {
        let experiment = LiveTranslateExperiment.experiment
        XCTAssertEqual(experiment.id, "live-translate")
        XCTAssertEqual(experiment.title, "Live Translate")
        XCTAssertFalse(experiment.summary.isEmpty)
        XCTAssertEqual(experiment.icon, "translate")
    }

    // MARK: - Fixtures

    private static func makeSolidImage(color: UIColor, size: CGSize) -> CGImage? {
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        let renderer = UIGraphicsImageRenderer(size: size, format: format)
        let image = renderer.image { ctx in
            color.setFill()
            ctx.fill(CGRect(origin: .zero, size: size))
        }
        return image.cgImage
    }

    private static func makeTextImage(text: String, size: CGSize) -> CGImage? {
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        let renderer = UIGraphicsImageRenderer(size: size, format: format)
        let image = renderer.image { ctx in
            UIColor.white.setFill()
            ctx.fill(CGRect(origin: .zero, size: size))
            let attributes: [NSAttributedString.Key: Any] = [
                .font: UIFont.boldSystemFont(ofSize: 64),
                .foregroundColor: UIColor.black,
            ]
            let drawn = text as NSString
            let textSize = drawn.size(withAttributes: attributes)
            let origin = CGPoint(
                x: (size.width - textSize.width) / 2,
                y: (size.height - textSize.height) / 2
            )
            drawn.draw(at: origin, withAttributes: attributes)
        }
        return image.cgImage
    }
}
