import CoreGraphics
import XCTest
@testable import Playground

final class LiveTranslateTrackingTests: XCTestCase {
    // MARK: - Text keys

    func testMatchKeyIgnoresCaseAccentsSpacingAndPunctuation() {
        XCTAssertEqual(LiveTranslateText.matchKey("  Café, del  MAR! "), "cafedelmar")
        XCTAssertEqual(LiveTranslateText.matchKey("CAFE DEL MAR"), "cafedelmar")
        XCTAssertEqual(LiveTranslateText.matchKey("出口"), "出口")
        XCTAssertEqual(LiveTranslateText.matchKey(" ¡¿ ?! "), "¡¿ ?!")
        XCTAssertEqual(LiveTranslateText.digits("mesa12a3"), "123")
    }

    func testSimilarityScoresEditDistance() {
        XCTAssertEqual(LiveTranslateText.similarity("salida", "salida"), 1)
        XCTAssertEqual(LiveTranslateText.similarity("salida", "sal1da"), 1 - 1.0 / 6, accuracy: 0.0001)
        XCTAssertEqual(LiveTranslateText.similarity("", ""), 1)
        XCTAssertEqual(LiveTranslateText.similarity("abc", ""), 0)
        XCTAssertEqual(
            LiveTranslateText.editDistance(Array("kitten".unicodeScalars), Array("sitting".unicodeScalars)),
            3
        )
    }

    func testPinnedTranslationSurvivesRereadsButNotNewDigits() {
        XCTAssertTrue(LiveTranslateText.canKeepTranslation(of: "Restaurante Mexicano", for: "Restaurante Mexicano Real"))
        XCTAssertFalse(LiveTranslateText.canKeepTranslation(of: "Mesa 12", for: "Mesa 13"))
        XCTAssertFalse(LiveTranslateText.canKeepTranslation(of: "Abierto", for: "Cerrado"))
    }

    // MARK: - Tracker

    func testTrackerKeepsLineIdentityThroughJitterMisreadsAndMisses() {
        var tracker = LiveTranslateTracker()
        tracker.update(with: [line("Salida", x: 0.1, y: 0.7), line("Entrada", x: 0.1, y: 0.4)])
        let first = ids(tracker)
        XCTAssertEqual(first.count, 2)
        XCTAssertFalse(tracker.tracks.contains(where: \.isSettled))

        tracker.update(with: [line("Salida", x: 0.11, y: 0.705), line("Entrada", x: 0.095, y: 0.398)])
        XCTAssertEqual(ids(tracker), first)
        XCTAssertTrue(tracker.tracks.allSatisfy(\.isSettled))

        tracker.update(with: [line("Sa1ida", x: 0.1, y: 0.7)])
        XCTAssertEqual(ids(tracker), first, "A misread keeps the line and its settled text")
        XCTAssertEqual(tracker.tracks.first { $0.id == first["Entrada"] }?.misses, 1)

        tracker.update(with: [line("Salida", x: 0.1, y: 0.7), line("Entrada", x: 0.1, y: 0.4)])
        XCTAssertEqual(ids(tracker), first)
        XCTAssertTrue(tracker.tracks.allSatisfy { $0.misses == 0 })
    }

    func testTrackerFollowsCameraPan() {
        var tracker = LiveTranslateTracker()
        let menu = [
            line("Menu del dia", x: 0.1, y: 0.8),
            line("Sopa de ajo", x: 0.1, y: 0.6),
            line("Pollo asado", x: 0.1, y: 0.4),
        ]
        tracker.update(with: menu)
        tracker.update(with: menu)
        let before = ids(tracker)

        // Too far to match by position alone. The shared shift lines them up.
        tracker.update(with: [
            line("Menu del dia", x: 0.35, y: 0.6),
            line("Sopa de ajo", x: 0.35, y: 0.4),
            line("Pollo asad0", x: 0.35, y: 0.2),
        ])
        XCTAssertEqual(tracker.tracks.count, 3)
        XCTAssertEqual(ids(tracker), before)
    }

    func testTrackerFollowsZoom() {
        var tracker = LiveTranslateTracker()
        let menu = [
            line("Menu del dia", x: 0.1, y: 0.8),
            line("Sopa de ajo", x: 0.1, y: 0.5),
            line("Pollo asado", x: 0.1, y: 0.2),
        ]
        tracker.update(with: menu)
        tracker.update(with: menu)
        let before = ids(tracker)

        // Outer lines spread apart by more than a line height, which one shared shift can't undo.
        tracker.update(with: menu.map { zoomed($0, by: 1.3) })
        XCTAssertEqual(tracker.tracks.count, 3)
        XCTAssertEqual(ids(tracker), before)
    }

    func testMotionFitsPanAndZoomAndComposes() {
        let points = [CGPoint(x: 0.2, y: 0.8), CGPoint(x: 0.6, y: 0.5), CGPoint(x: 0.3, y: 0.2)]
        let truth = LiveTranslateMotion(scale: 1.2, dx: -0.05, dy: 0.03)
        let fitted = LiveTranslateMotion.fit(
            points.map { (from: $0, to: truth.apply(to: $0)) },
            minimumSpan: 0.03,
            scaleRange: 0.5...2
        )
        XCTAssertEqual(fitted.scale, 1.2, accuracy: 0.0001)
        XCTAssertEqual(fitted.dx, -0.05, accuracy: 0.0001)
        XCTAssertEqual(fitted.dy, 0.03, accuracy: 0.0001)

        let single = LiveTranslateMotion.fit([(from: points[0], to: CGPoint(x: 0.25, y: 0.7))], minimumSpan: 0.03, scaleRange: 0.5...2)
        XCTAssertEqual(single.scale, 1)
        XCTAssertEqual(single.dx, 0.05, accuracy: 0.0001)
        XCTAssertEqual(single.dy, -0.1, accuracy: 0.0001)
        XCTAssertEqual(LiveTranslateMotion.fit([], minimumSpan: 0.03, scaleRange: 0.5...2), .identity)

        let step = LiveTranslateMotion(scale: 1.1, dx: 0.02, dy: 0)
        let point = CGPoint(x: 0.4, y: 0.6)
        let twice = step.then(truth).apply(to: point)
        let expected = truth.apply(to: step.apply(to: point))
        XCTAssertEqual(twice.x, expected.x, accuracy: 0.0001)
        XCTAssertEqual(twice.y, expected.y, accuracy: 0.0001)
    }

    func testDisplayBoxIgnoresBlurThatSwellsABoxForAPass() throws {
        var tracker = LiveTranslateTracker()
        let steady = line("Prohibido fumar", x: 0.3, y: 0.5, width: 0.35, height: 0.02)
        for _ in 0..<3 {
            tracker.update(with: [steady])
        }
        let settled = try XCTUnwrap(tracker.tracks.first?.displayBox)

        // Blur swells the box 70% on one pass and 30% on the next, around the same center.
        for swell in [1.7, 1.3] {
            let box = steady.boundingBox
            tracker.update(with: [line(
                "Prohibido fumar",
                x: box.midX - box.width * 0.55,
                y: box.midY - box.height * swell / 2,
                width: box.width * 1.1,
                height: box.height * swell
            )])
            let shown = try XCTUnwrap(tracker.tracks.first?.displayBox)
            XCTAssertEqual(shown.height / settled.height, 1, accuracy: 0.06, "swell \(swell)")
            XCTAssertEqual(shown.midY, box.midY, accuracy: 0.001)
        }
        tracker.update(with: [steady])
        tracker.update(with: [steady])
        let after = try XCTUnwrap(tracker.tracks.first?.displayBox)
        XCTAssertEqual(after.height / settled.height, 1, accuracy: 0.03)
    }

    func testDisplayBoxKeepsCoveringALinePartlyRead() throws {
        var tracker = LiveTranslateTracker()
        let full = line("Solo personal autorizado", x: 0.25, y: 0.4, width: 0.5, height: 0.025)
        tracker.update(with: [full])
        tracker.update(with: [full])

        // Glare hides "autorizado": OCR returns the left part only.
        tracker.update(with: [line("Solo personal", x: 0.25, y: 0.401, width: 0.28, height: 0.025)])
        let shown = try XCTUnwrap(tracker.tracks.first?.displayBox)
        XCTAssertEqual(tracker.tracks.count, 1)
        XCTAssertEqual(shown.minX, 0.25, accuracy: 0.01)
        XCTAssertEqual(shown.maxX, 0.75, accuracy: 0.01)
        XCTAssertEqual(shown.midY, 0.401 + 0.0125, accuracy: 0.001)
    }

    func testDisplayBoxScalesWithZoomRightAway() throws {
        var tracker = LiveTranslateTracker()
        let menu = [
            line("Menu del dia", x: 0.1, y: 0.8),
            line("Sopa de ajo", x: 0.1, y: 0.5),
            line("Pollo asado", x: 0.1, y: 0.2),
        ]
        tracker.update(with: menu)
        tracker.update(with: menu)
        let before = Dictionary(uniqueKeysWithValues: tracker.tracks.map { ($0.text, $0.displayBox.height) })

        tracker.update(with: menu.map { zoomed($0, by: 1.3) })
        for track in tracker.tracks {
            let ratio = track.displayBox.height / (before[track.text] ?? 1)
            XCTAssertEqual(ratio, 1.3, accuracy: 0.05, track.text)
        }
    }

    func testDisplayBoxAdoptsALastingSizeChange() throws {
        var tracker = LiveTranslateTracker()
        let small = line("Salida", x: 0.4, y: 0.5, width: 0.2, height: 0.03)
        tracker.update(with: [small])
        tracker.update(with: [small])
        let bigger = line("Salida", x: 0.38, y: 0.4925, width: 0.24, height: 0.045)
        for _ in 0..<6 {
            tracker.update(with: [bigger])
        }
        let shown = try XCTUnwrap(tracker.tracks.first?.displayBox)
        XCTAssertEqual(shown.height, 0.045, accuracy: 0.0045)
    }

    func testTrackerDropsOneOffReadingsAndExpiredLines() {
        var tracker = LiveTranslateTracker()
        tracker.update(with: [line("Hola", x: 0.1, y: 0.6), line("x7#", x: 0.5, y: 0.2, width: 0.1)])
        tracker.update(with: [line("Hola", x: 0.1, y: 0.6)])
        XCTAssertEqual(tracker.tracks.map(\.text), ["Hola"])

        for _ in 0..<LiveTranslateTracker.maximumMisses {
            tracker.update(with: [])
        }
        XCTAssertEqual(tracker.tracks.map(\.text), ["Hola"])
        tracker.update(with: [])
        XCTAssertTrue(tracker.tracks.isEmpty)
    }

    func testTrackerStartsNewLineWhenTextChangesInPlace() {
        var tracker = LiveTranslateTracker()
        tracker.update(with: [line("Abierto", x: 0.2, y: 0.5)])
        tracker.update(with: [line("Abierto", x: 0.2, y: 0.5)])
        let openID = tracker.tracks.first?.id

        // One pass of new text could be noise, so the old line stays for now.
        tracker.update(with: [line("Cerrado", x: 0.2, y: 0.5)])
        XCTAssertEqual(Set(tracker.tracks.map(\.text)), ["Abierto", "Cerrado"])

        tracker.update(with: [line("Cerrado", x: 0.2, y: 0.5)])
        XCTAssertEqual(tracker.tracks.map(\.text), ["Cerrado"])
        XCTAssertNotEqual(tracker.tracks.first?.id, openID)
    }

    func testTrackerKeepsRepeatedTextApart() throws {
        var tracker = LiveTranslateTracker()
        let prices = [
            line("$5", x: 0.6, y: 0.7, width: 0.1),
            line("$5", x: 0.6, y: 0.3, width: 0.1),
        ]
        tracker.update(with: prices)
        tracker.update(with: prices)
        let top = try XCTUnwrap(tracker.tracks.first?.id)
        let bottom = try XCTUnwrap(tracker.tracks.last?.id)
        XCTAssertNotEqual(top, bottom)

        tracker.update(with: [
            line("$5", x: 0.61, y: 0.68, width: 0.1),
            line("$5", x: 0.61, y: 0.28, width: 0.1),
        ])
        XCTAssertEqual(tracker.tracks.map(\.id), [top, bottom])
    }

    // MARK: - Memory

    func testMemoryMatchesCaseAccentsAndSpacingPerLanguage() {
        var memory = LiveTranslateMemory()
        memory.remember(source: "Café  del Mar", translation: " Sea  Cafe ", language: .english)
        XCTAssertEqual(memory.translation(for: "CAFE DEL MAR", language: .english), "Sea Cafe")
        XCTAssertEqual(memory.translation(for: "café del mar!", language: .english), "Sea Cafe")
        XCTAssertNil(memory.translation(for: "Café del Mar", language: .french))
        XCTAssertEqual(memory.count(for: .english), 1)
    }

    func testMemoryReusesNearReadingsOnlyWhenDigitsMatch() {
        var memory = LiveTranslateMemory()
        memory.remember(source: "Salida de emergencia", translation: "Emergency exit", language: .english)
        memory.remember(source: "Mesa 12 reservada", translation: "Table 12 reserved", language: .english)
        XCTAssertEqual(memory.translation(for: "Salida de emergencla", language: .english), "Emergency exit")
        XCTAssertNil(memory.translation(for: "Mesa 13 reservada", language: .english))
        XCTAssertNil(memory.translation(for: "Salida", language: .english))
    }

    func testMemoryDropsOldestEntryPastCapacity() {
        var memory = LiveTranslateMemory()
        for index in 0...LiveTranslateMemory.capacity {
            memory.remember(source: "line \(index)", translation: "L\(index)", language: .english)
        }
        XCTAssertEqual(memory.count(for: .english), LiveTranslateMemory.capacity)
        XCTAssertNil(memory.translation(for: "line 0", language: .english))
        XCTAssertEqual(memory.translation(for: "line 1", language: .english), "L1")
    }

    func testMemoryBacksOffFailedLinesUntilTranslated() {
        var memory = LiveTranslateMemory()
        let start = Date(timeIntervalSinceReferenceDate: 1_000)
        memory.recordFailure(source: "Zzz", language: .english, at: start)
        XCTAssertTrue(memory.isBlocked(source: "zzz", language: .english, at: start.addingTimeInterval(1)))
        XCTAssertFalse(memory.isBlocked(source: "zzz", language: .english, at: start.addingTimeInterval(2)))
        XCTAssertFalse(memory.isBlocked(source: "zzz", language: .french, at: start))

        memory.recordFailure(source: "Zzz", language: .english, at: start.addingTimeInterval(3))
        XCTAssertTrue(memory.isBlocked(source: "Zzz", language: .english, at: start.addingTimeInterval(6.5)))
        XCTAssertFalse(memory.isBlocked(source: "Zzz", language: .english, at: start.addingTimeInterval(7)))

        memory.recordFailure(source: "Zzz", language: .english, at: start.addingTimeInterval(8))
        memory.remember(source: "Zzz", translation: "Sleep", language: .english)
        XCTAssertFalse(memory.isBlocked(source: "Zzz", language: .english, at: start.addingTimeInterval(8)))
    }

    // MARK: - Batches and overlays

    func testTranslationBatchTakesSettledUntranslatedLinesOnce() {
        var memory = LiveTranslateMemory()
        let now = Date()
        memory.remember(source: "Adiós", translation: "Goodbye", language: .english)
        memory.recordFailure(source: "Gracias", language: .english, at: now)
        let tracks = [
            track("a", "Hola", y: 0.8),
            track("b", "Adiós", y: 0.7),
            track("c", "hola", y: 0.6),
            track("d", "Gracias", y: 0.5),
            track("e", "Nuevo", hits: 1, y: 0.4),
            track("f", "Perdido", misses: 1, y: 0.3),
            track("g", "Por favor", y: 0.2),
        ]
        XCTAssertEqual(
            LiveTranslateResultBuilder.translationBatch(tracks: tracks, memory: memory, language: .english, now: now),
            ["Hola", "Por favor"]
        )
        XCTAssertEqual(
            LiveTranslateResultBuilder.translationBatch(
                tracks: tracks,
                memory: memory,
                language: .english,
                now: now,
                maxCount: 1
            ),
            ["Hola"]
        )
    }

    func testTranslationBatchRetriesFailedLinesAlone() {
        var memory = LiveTranslateMemory()
        let start = Date(timeIntervalSinceReferenceDate: 1_000)
        memory.recordFailure(source: "Uno", language: .english, at: start)
        memory.recordFailure(source: "Dos", language: .english, at: start)
        let tracks = [track("a", "Uno", y: 0.8), track("b", "Dos", y: 0.6), track("c", "Tres", y: 0.4)]
        func batch(at now: Date) -> [String] {
            LiveTranslateResultBuilder.translationBatch(tracks: tracks, memory: memory, language: .english, now: now)
        }

        XCTAssertEqual(batch(at: start), ["Tres"])
        let later = start.addingTimeInterval(LiveTranslateMemory.firstRetryDelay)
        XCTAssertEqual(batch(at: later), ["Uno"])
        memory.remember(source: "Uno", translation: "One", language: .english)
        XCTAssertEqual(batch(at: later), ["Dos"])
    }

    func testOverlaysShowStoredTranslationsAndHideUnsettledReadings() {
        var memory = LiveTranslateMemory()
        memory.remember(source: "Hola", translation: "Hello", language: .english)
        var pins: [String: LiveTranslatePin] = [:]
        let tracks = [
            track("a", "Hola", hits: 1, y: 0.8),
            track("b", "Mundo", y: 0.6),
            track("c", "Ruido", hits: 1, y: 0.4),
        ]
        let overlays = LiveTranslateResultBuilder.overlays(
            tracks: tracks,
            memory: memory,
            language: .english,
            pins: &pins
        )
        XCTAssertEqual(overlays.map(\.id), ["a", "b"])
        XCTAssertEqual(overlays.map(\.displayText), ["Hello", "Mundo"])
        XCTAssertEqual(overlays.map(\.isTranslated), [true, false])
        XCTAssertEqual(pins, ["a": LiveTranslatePin(source: "Hola", translation: "Hello", language: .english)])

        let french = LiveTranslateResultBuilder.overlays(
            tracks: tracks,
            memory: memory,
            language: .french,
            pins: &pins
        )
        XCTAssertEqual(french.map(\.id), ["b"])
        XCTAssertTrue(pins.isEmpty)
    }

    func testOverlaysKeepPinnedTranslationWhileChangedReadingWaits() {
        var memory = LiveTranslateMemory()
        memory.remember(source: "Restaurante Mexicano", translation: "Mexican Restaurant", language: .english)
        var pins: [String: LiveTranslatePin] = [:]
        _ = LiveTranslateResultBuilder.overlays(
            tracks: [track("a", "Restaurante Mexicano")],
            memory: memory,
            language: .english,
            pins: &pins
        )

        let grown = LiveTranslateResultBuilder.overlays(
            tracks: [track("a", "Restaurante Mexicano Real")],
            memory: memory,
            language: .english,
            pins: &pins
        )
        XCTAssertEqual(grown.first?.displayText, "Mexican Restaurant")
        XCTAssertEqual(grown.first?.isTranslated, true)

        let renumbered = LiveTranslateResultBuilder.overlays(
            tracks: [track("a", "Restaurante Mexicano 2")],
            memory: memory,
            language: .english,
            pins: &pins
        )
        XCTAssertEqual(renumbered.first?.isTranslated, false)
        XCTAssertTrue(pins.isEmpty)
    }

    func testOverlaysHideMissedLineUnderShownReading() {
        var memory = LiveTranslateMemory()
        memory.remember(source: "Salida de emergencia", translation: "Emergency exit", language: .english)
        memory.remember(source: "Salida de", translation: "Exit of", language: .english)
        var pins: [String: LiveTranslatePin] = [:]
        let missed = track("a", "Salida de emergencia", misses: 1)
        let split = track("b", "Salida de", hits: 1)

        let shown = LiveTranslateResultBuilder.overlays(
            tracks: [missed, split],
            memory: memory,
            language: .english,
            pins: &pins
        )
        XCTAssertEqual(shown.map(\.id), ["b"])

        let noise = track("c", "Sxlxdx", hits: 1)
        let kept = LiveTranslateResultBuilder.overlays(
            tracks: [missed, noise],
            memory: memory,
            language: .english,
            pins: &pins
        )
        XCTAssertEqual(kept.map(\.displayText), ["Emergency exit"], "A hidden one-pass reading doesn't cover it")
    }

    func testBackdropBlendMovesPartwayTowardSample() {
        let dark = LiveTranslateBackdrop(red: 0, green: 0, blue: 0, luma: 0)
        let light = LiveTranslateBackdrop(red: 1, green: 1, blue: 1, luma: 1)
        let blended = dark.blended(toward: light, weight: 0.25)
        XCTAssertEqual(blended.red, 0.25, accuracy: 0.0001)
        XCTAssertEqual(blended.luma, 0.25, accuracy: 0.0001)
    }

    // MARK: - Streamed replies

    func testFinishedTranslationsWaitForTheNextItemWhileStreaming() {
        let expected = ["Hola", "Mundo", "Adiós"]
        let partial: [(source: String?, translation: String?)] = [
            (source: "Hola", translation: "Hello"),
            (source: "Mundo", translation: "Wor"),
        ]
        XCTAssertEqual(
            LiveTranslateResultBuilder.finishedTranslations(items: partial, expected: expected, isFinal: false),
            [0: "Hello"]
        )
        XCTAssertEqual(
            LiveTranslateResultBuilder.finishedTranslations(items: partial, expected: expected, isFinal: true),
            [0: "Hello", 1: "Wor"]
        )
        XCTAssertEqual(
            LiveTranslateResultBuilder.finishedTranslations(items: [], expected: expected, isFinal: false),
            [:]
        )
    }

    func testFinishedTranslationsRealignWhenTheModelSkipsALine() {
        let items: [(source: String?, translation: String?)] = [
            (source: "Hola", translation: " Hello "),
            (source: "Adios", translation: "Goodbye"),
            (source: nil, translation: "   "),
        ]
        XCTAssertEqual(
            LiveTranslateResultBuilder.finishedTranslations(
                items: items,
                expected: ["Hola", "Mundo", "Adiós"],
                isFinal: true
            ),
            [0: "Hello", 2: "Goodbye"]
        )
    }

    func testFinishedTranslationsFallBackToPositionWhenTheEchoIsOff() {
        let items: [(source: String?, translation: String?)] = [
            (source: "Hello", translation: "Hello"),
            (source: "", translation: "World"),
        ]
        XCTAssertEqual(
            LiveTranslateResultBuilder.finishedTranslations(items: items, expected: ["Hola", "Mundo"], isFinal: true),
            [0: "Hello", 1: "World"]
        )
    }

    // MARK: - Fixtures

    private func line(
        _ text: String,
        x: Double,
        y: Double,
        width: Double = 0.4,
        height: Double = 0.05,
        confidence: Double = 0.9
    ) -> LiveTranslateObservation {
        LiveTranslateObservation(
            text: text,
            confidence: confidence,
            boundingBox: CGRect(x: x, y: y, width: width, height: height)
        )
    }

    /// `observation` as seen after the camera moves closer, scaling about the frame center.
    private func zoomed(_ observation: LiveTranslateObservation, by scale: CGFloat) -> LiveTranslateObservation {
        let box = observation.boundingBox
        return LiveTranslateObservation(
            text: observation.text,
            confidence: observation.confidence,
            boundingBox: CGRect(
                x: 0.5 + (box.minX - 0.5) * scale,
                y: 0.5 + (box.minY - 0.5) * scale,
                width: box.width * scale,
                height: box.height * scale
            )
        )
    }

    private func track(
        _ id: String,
        _ text: String,
        hits: Int = LiveTranslateTracker.settleHits,
        misses: Int = 0,
        y: Double = 0.5
    ) -> LiveTranslateTrack {
        let box = CGRect(x: 0.1, y: y, width: 0.4, height: 0.05)
        return LiveTranslateTrack(
            id: id,
            text: text,
            key: LiveTranslateText.matchKey(text),
            boundingBox: box,
            displayBox: box,
            hits: hits,
            misses: misses,
            votes: [text: 1]
        )
    }

    /// Track id by settled text. Only for frames whose lines all differ.
    private func ids(_ tracker: LiveTranslateTracker) -> [String: String] {
        Dictionary(uniqueKeysWithValues: tracker.tracks.map { ($0.text, $0.id) })
    }
}
