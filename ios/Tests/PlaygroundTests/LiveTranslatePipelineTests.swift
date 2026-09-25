import CoreGraphics
import XCTest
@testable import Playground

final class LiveTranslatePipelineTests: XCTestCase {
    private let start = Date(timeIntervalSinceReferenceDate: 1_000)

    func testBatchesRunOneAtATimeAndUntranslatedLinesBackOff() throws {
        var pipeline = settledPipeline(["Hola", "Mundo"])
        let batch = try XCTUnwrap(pipeline.nextBatch(now: start))
        XCTAssertEqual(batch.sources, ["Hola", "Mundo"])
        XCTAssertTrue(pipeline.isTranslating)
        XCTAssertNil(pipeline.nextBatch(now: start), "One batch at a time")

        pipeline.receive([0: "Hello"], for: batch)
        XCTAssertEqual(pipeline.overlays.map(\.displayText), ["Hello", "Mundo"])

        XCTAssertTrue(pipeline.finish(batch, translations: [:], now: start))
        XCTAssertFalse(pipeline.isTranslating)
        XCTAssertNil(pipeline.nextBatch(now: start), "Mundo waits after the model skipped it")
        let retry = try XCTUnwrap(pipeline.nextBatch(now: start.addingTimeInterval(LiveTranslateMemory.firstRetryDelay)))
        XCTAssertEqual(retry.sources, ["Mundo"])
    }

    func testCanceledBatchStillStoresItsTranslations() throws {
        var pipeline = settledPipeline(["Hola"])
        let batch = try XCTUnwrap(pipeline.nextBatch(now: start))
        pipeline.cancelBatch()
        XCTAssertFalse(pipeline.isTranslating)

        XCTAssertFalse(pipeline.finish(batch, translations: [0: "Hello"], now: start))
        XCTAssertEqual(pipeline.overlays.map(\.displayText), ["Hello"])
        XCTAssertNil(pipeline.nextBatch(now: start))
    }

    func testLanguageChangeDropsTheBatchAndShowsThatLanguagesTranslations() throws {
        var pipeline = settledPipeline(["Hola"])
        let english = try XCTUnwrap(pipeline.nextBatch(now: start))
        pipeline.receive([0: "Hello"], for: english)

        pipeline.setLanguage(.french)
        XCTAssertFalse(pipeline.isTranslating)
        XCTAssertEqual(pipeline.overlays.map(\.isTranslated), [false])
        let french = try XCTUnwrap(pipeline.nextBatch(now: start))
        XCTAssertEqual(french.language, .french)
        XCTAssertFalse(pipeline.finish(english, translations: [:], now: start), "The English batch no longer counts")
        pipeline.finish(french, translations: [0: "Bonjour"], now: start)
        XCTAssertEqual(pipeline.overlays.map(\.displayText), ["Bonjour"])

        pipeline.setLanguage(.english)
        XCTAssertEqual(pipeline.overlays.map(\.displayText), ["Hello"])
        XCTAssertNil(pipeline.nextBatch(now: start))
    }

    func testBackdropsSampleLinesReadThisPassAndKeepMissedOnes() {
        var pipeline = settledPipeline(["Hola", "Mundo"])
        let light = LiveTranslateBackdrop(red: 1, green: 1, blue: 1, luma: 1)
        pipeline.sampleBackdrops { _ in light }
        pipeline.ingest([line("Hola", y: 0.7)])
        pipeline.sampleBackdrops { _ in LiveTranslateBackdrop(red: 0, green: 0, blue: 0, luma: 0) }

        let backdrops = Dictionary(uniqueKeysWithValues: pipeline.overlays.map { ($0.sourceText, $0.backdrop.luma) })
        XCTAssertEqual(backdrops["Hola"] ?? -1, 0.5, accuracy: 0.0001, "Blended toward the new sample")
        XCTAssertEqual(backdrops["Mundo"] ?? -1, 1, accuracy: 0.0001, "Missed this pass, so unchanged")
    }

    func testClearTrackingKeepsTranslations() throws {
        var pipeline = settledPipeline(["Hola"])
        let batch = try XCTUnwrap(pipeline.nextBatch(now: start))
        pipeline.finish(batch, translations: [0: "Hello"], now: start)

        pipeline.clearTracking()
        XCTAssertTrue(pipeline.overlays.isEmpty)
        pipeline.ingest([line("Hola", y: 0.7)])
        XCTAssertEqual(pipeline.overlays.map(\.displayText), ["Hello"], "Remembered on the first pass back")
    }

    /// A hand-held camera rarely reads the same set of lines twice in a row. A
    /// translation that lands several passes after it was requested still has
    /// to show on every later pass that reads those lines.
    func testTranslationsLandAndStayWhileFramesKeepChanging() {
        let texts = ["Salida de emergencia", "No fumar", "Prohibido el paso"]
        func frame(_ step: Int) -> [LiveTranslateObservation] {
            let dx = 0.004 * Double(step) + 0.01 * Double(step % 3)
            let dy = -0.006 * Double(step)
            var lines: [LiveTranslateObservation] = []
            for (row, text) in texts.enumerated() where (step + row) % 4 != 3 {
                let reading = row == 0 && step % 5 == 2 ? "Salida de emergencla" : text
                lines.append(line(
                    reading,
                    x: 0.1 + dx,
                    y: 0.7 - 0.15 * Double(row) + dy,
                    confidence: 0.6 + 0.1 * Double(row)
                ))
            }
            return lines
        }

        var pipeline = LiveTranslatePipeline()
        var model = LiveTranslateFakeModel()
        var firstShown: Int?
        for step in 0..<20 {
            model.step(pass: step, observations: frame(step), pipeline: &pipeline)
            let shown = Set(pipeline.overlays.filter(\.isTranslated).map(\.displayText))
            if firstShown == nil, !shown.isEmpty {
                firstShown = step
            }
            if let firstShown, step > firstShown {
                XCTAssertTrue(
                    shown.isSuperset(of: ["EN Salida de emergencia", "EN No fumar"]),
                    "step \(step): \(shown)"
                )
            }
            if step >= 12 {
                XCTAssertEqual(pipeline.overlays.count, texts.count, "step \(step)")
                XCTAssertEqual(shown, Set(texts.map { "EN \($0)" }), "step \(step)")
            }
        }
        XCTAssertNotNil(firstShown)
        XCTAssertLessThanOrEqual(model.started.count, 3, "\(model.started.map(\.sources))")
    }

    // MARK: - Fixtures

    /// A pipeline whose lines have been read twice, so they are ready for the model.
    private func settledPipeline(_ texts: [String]) -> LiveTranslatePipeline {
        var pipeline = LiveTranslatePipeline()
        let observations = texts.enumerated().map { index, text in
            line(text, y: 0.7 - 0.15 * Double(index))
        }
        pipeline.ingest(observations)
        pipeline.ingest(observations)
        return pipeline
    }

    private func line(_ text: String, x: Double = 0.1, y: Double, confidence: Double = 0.9) -> LiveTranslateObservation {
        LiveTranslateObservation(
            text: text,
            confidence: confidence,
            boundingBox: CGRect(x: x, y: y, width: 0.4, height: 0.05)
        )
    }
}
