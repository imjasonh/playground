import UIKit
import XCTest
@testable import Playground

@MainActor
final class BlatherTests: XCTestCase {
    private var directory: URL!

    override func setUpWithError() throws {
        directory = FileManager.default.temporaryDirectory
            .appendingPathComponent("blather-tests-\(UUID().uuidString)", isDirectory: true)
    }

    override func tearDownWithError() throws {
        if let directory {
            try? FileManager.default.removeItem(at: directory)
        }
    }

    func testCleanStripsMarkupAndStageDirections() {
        let cleaned = BlatherScript.clean(
            """
            # Tide pools
            **Barnacles** hold on.
            - They wait for the tide.
            (music)
            [applause]
            Host: The water returns.
            """
        )
        XCTAssertFalse(cleaned.contains("#"))
        XCTAssertFalse(cleaned.contains("**"))
        XCTAssertFalse(cleaned.contains("(music)"))
        XCTAssertFalse(cleaned.contains("[applause]"))
        XCTAssertFalse(cleaned.contains("Host:"))
        XCTAssertTrue(cleaned.contains("Tide pools"))
        XCTAssertTrue(cleaned.contains("Barnacles hold on."))
        XCTAssertTrue(cleaned.contains("They wait for the tide."))
        XCTAssertTrue(cleaned.contains("The water returns."))
    }

    func testCleanDropsWrappingQuotesAndClipsToASentence() {
        let quoted = BlatherScript.clean("\"A complete sentence.\"")
        XCTAssertEqual(quoted, "A complete sentence.")

        let long = String(repeating: "word ", count: 200) + "End here. And more after the limit."
        let clipped = BlatherScript.clean(long)
        XCTAssertLessThanOrEqual(clipped.count, BlatherScript.maxSpeechCharacters)
        XCTAssertTrue(clipped.hasSuffix("."))
    }

    func testTailStartsAfterASentenceBoundary() {
        let speech = "Short start. " + String(repeating: "a", count: 500) + ". The rest of the thought stays."
        let tail = BlatherScript.tail(of: speech, maxCharacters: 80)
        XCTAssertTrue(tail.hasPrefix("The rest"))
        XCTAssertLessThan(tail.count, speech.count)
    }

    func testOpeningAndContinuationPrompts() {
        let opening = BlatherScript.opening(topic: "glaciers", directions: ["mention ice cores"])
        XCTAssertTrue(opening.contains("Topic: glaciers"))
        XCTAssertTrue(opening.contains("ice cores"))

        let next = BlatherScript.continuation(
            topic: "glaciers",
            directions: [],
            tail: "The ice moves."
        )
        XCTAssertTrue(next.contains("Continue the explainer"))
        XCTAssertTrue(next.contains("The ice moves."))
    }

    func testClockLabels() {
        XCTAssertEqual(BlatherClock.label(0), "0:00")
        XCTAssertEqual(BlatherClock.label(65), "1:05")
        XCTAssertEqual(BlatherClock.label(3661), "1:01:01")
    }

    func testSkipPrefetchAndCut() {
        XCTAssertEqual(BlatherTimeline.skipped(5, by: -10, duration: 40), 0)
        XCTAssertEqual(BlatherTimeline.skipped(35, by: 10, duration: 40), 40)
        XCTAssertFalse(BlatherTimeline.shouldPrefetch(playhead: 0, duration: 40))
        XCTAssertTrue(BlatherTimeline.shouldPrefetch(playhead: 20, duration: 40))
        XCTAssertTrue(BlatherTimeline.needsOpeningAudio(playhead: 0, duration: 39))
        XCTAssertFalse(BlatherTimeline.needsOpeningAudio(playhead: 0, duration: 40))
        XCTAssertTrue(BlatherTimeline.needsOpeningAudio(playhead: 10, duration: 49))
        XCTAssertTrue(BlatherTimeline.needsOpeningAudio(playhead: 0, duration: 79, rate: 2))
        XCTAssertFalse(BlatherTimeline.needsOpeningAudio(playhead: 0, duration: 80, rate: 2))
        XCTAssertEqual(BlatherTimeline.estimatedDuration(of: "one two three"), 1, accuracy: 0.001)
        XCTAssertTrue(BlatherModelFailure.isInterrupted(
            domain: "FoundationModels.LanguageModelError",
            code: -1,
            description: "The operation couldn’t be completed. (FoundationModels.LanguageModelError error -1.)"
        ))
        XCTAssertFalse(BlatherModelFailure.isInterrupted(
            domain: "FoundationModels.LanguageModelError",
            code: 1,
            description: "The context window was exceeded."
        ))
        XCTAssertFalse(BlatherTimeline.shouldPrefetch(playhead: 0, duration: 60, rate: 2))
        XCTAssertTrue(BlatherTimeline.shouldPrefetch(playhead: 0, duration: 40, rate: 2))

        let first = segment(text: "One.", duration: 30, fileName: "a.caf")
        let second = segment(text: "Two.", duration: 20, fileName: "b.caf")
        let mid = BlatherTimeline.cut(segments: [first, second], at: 12)
        XCTAssertEqual(mid.segments.map(\.duration), [12])
        XCTAssertEqual(mid.removedFileNames, ["b.caf"])
        XCTAssertEqual(mid.playhead, 12)

        let start = BlatherTimeline.cut(segments: [first, second], at: 0)
        XCTAssertTrue(start.segments.isEmpty)
        XCTAssertEqual(start.removedFileNames, ["a.caf", "b.caf"])

        let located = BlatherTimeline.locate(30, durations: [30, 20])
        XCTAssertEqual(located.index, 1)
        XCTAssertEqual(located.offset, 0)
    }

    func testPlannerCompactsWhenForced() {
        var planner = BlatherPlanner()
        let first = planner.makeRequest(topic: "tides", directions: [], spoken: [])
        XCTAssertFalse(first.freshSession)
        XCTAssertFalse(first.didCompact)
        planner.commit(prompt: first.prompt, speech: "The sea rises.", measuredTotalTokens: nil)

        planner.forceCompact()
        let compacted = planner.makeRequest(
            topic: "tides",
            directions: ["shorter sentences"],
            spoken: ["The sea rises."]
        )
        XCTAssertTrue(compacted.freshSession)
        XCTAssertTrue(compacted.didCompact)
        XCTAssertTrue(compacted.prompt.contains("tides"))
        XCTAssertTrue(compacted.prompt.contains("shorter sentences"))
    }

    func testArtworkDependsOnTheTopic() {
        let glaciers = BlatherArtwork.render(topic: "glaciers", pixels: 80)
        let again = BlatherArtwork.render(topic: "glaciers", pixels: 80)
        let kelp = BlatherArtwork.render(topic: "kelp", pixels: 80)
        XCTAssertEqual(colorGrid(glaciers), colorGrid(again))
        XCTAssertNotEqual(colorGrid(glaciers), colorGrid(kelp))
        XCTAssertGreaterThan(Set(colorGrid(glaciers)).count, 1)
        let jpeg = BlatherArtwork.jpeg(topic: "glaciers", pixels: 80)
        XCTAssertTrue(jpeg.starts(with: [0xFF, 0xD8]))
        XCTAssertEqual(UIImage(data: jpeg)?.size, CGSize(width: 80, height: 80))
    }

    func testRefreshBackfillsAMissingCover() throws {
        let store = BlatherStore(root: directory)
        let id = UUID()
        let episode = BlatherEpisode(
            id: id,
            topic: "owls",
            createdAt: Date(timeIntervalSince1970: 10),
            updatedAt: Date(timeIntervalSince1970: 20),
            directions: [],
            segments: []
        )
        try store.save(episode)
        XCTAssertFalse(store.hasCover(episodeID: id))
        let session = makeSession(
            narrator: FakeNarrator(text: "Hi."),
            synthesizer: FakeSynthesizer(duration: 40),
            playback: FakePlayback(),
            store: store
        )
        session.refresh()
        XCTAssertTrue(store.hasCover(episodeID: id))
        let first = try Data(contentsOf: store.coverURL(episodeID: id))
        session.refresh()
        XCTAssertEqual(try Data(contentsOf: store.coverURL(episodeID: id)), first)
    }

    func testStoreRoundTrip() throws {
        let store = BlatherStore(root: directory)
        let id = UUID()
        var episode = BlatherEpisode(
            id: id,
            topic: "kelp",
            createdAt: Date(timeIntervalSince1970: 10),
            updatedAt: Date(timeIntervalSince1970: 20),
            directions: ["slower"],
            segments: [segment(text: "Kelp grows.", duration: 12, fileName: "one.caf")]
        )
        try store.save(episode)
        try Data("audio".utf8).write(to: store.audioURL(episodeID: id, fileName: "one.caf"))
        XCTAssertEqual(store.load(id: id), episode)
        XCTAssertEqual(store.summaries().map(\.id), [id])
        XCTAssertEqual(store.summaries().first?.duration, 12)

        episode.topic = "kelp forests"
        episode.updatedAt = Date(timeIntervalSince1970: 30)
        try store.save(episode)
        XCTAssertEqual(store.load(id: id)?.topic, "kelp forests")

        store.delete(id: id)
        XCTAssertNil(store.load(id: id))
        XCTAssertTrue(store.summaries().isEmpty)
    }

    func testStartPlaysAndPrefetchesNearTheEnd() async {
        let speech = manyWords()
        let narrator = FakeNarrator(text: speech)
        let synthesizer = FakeSynthesizer(duration: 40)
        let playback = FakePlayback()
        let session = makeSession(narrator: narrator, synthesizer: synthesizer, playback: playback)

        await session.start(topic: "  glaciers  ")
        XCTAssertEqual(session.mode, .live)
        XCTAssertEqual(session.episode?.topic, "glaciers")
        XCTAssertEqual(session.episode?.segments.count, 1)
        XCTAssertEqual(session.episode?.segments.first?.text, speech)
        XCTAssertEqual(session.episode?.segments.first?.duration, 40)
        XCTAssertTrue(session.isPlaying)
        XCTAssertFalse(session.isGenerating)
        XCTAssertEqual(narrator.prompts.count, 1)
        XCTAssertTrue(narrator.prompts[0].contains("glaciers"))
        XCTAssertEqual(playback.updates.last?.playing, true as Bool?)
        XCTAssertEqual(session.saved.count, 1)
        if let id = session.episode?.id {
            XCTAssertTrue(BlatherStore(root: directory).hasCover(episodeID: id))
        } else {
            XCTFail("Missing episode")
        }

        session.setSpeed(.x1_5)
        XCTAssertEqual(session.speed, .x1_5)
        XCTAssertEqual(playback.updates.last?.rate, 1.5)
        session.setSpeed(.x1_75)
        XCTAssertEqual(playback.updates.last?.rate, 1.75)
        session.setSpeed(.x2)
        XCTAssertEqual(playback.updates.last?.rate, 2)
        session.setSpeed(.x1)
        XCTAssertEqual(playback.updates.last?.rate, 1)
        XCTAssertEqual(playback.updates.last?.playing, true as Bool?)

        session.seek(to: 12)
        XCTAssertEqual(session.playhead, 12)
        session.seek(to: -5)
        XCTAssertEqual(session.playhead, 0)
        session.skip(by: 20)
        await session.waitForFill()
        XCTAssertEqual(session.playhead, 20)
        XCTAssertEqual(session.episode?.segments.count, 2)
        XCTAssertEqual(narrator.prompts.count, 2)
        XCTAssertTrue(narrator.prompts[1].contains("Continue the explainer"))
        XCTAssertEqual(session.audibleDuration, 80)
    }

    func testStartBuffersAboutFortySecondsBeforePlayback() async {
        let playback = FakePlayback()
        let session = makeSession(
            narrator: FakeNarrator(text: "A short passage."),
            synthesizer: FakeSynthesizer(duration: 15),
            playback: playback
        )

        await session.start(topic: "tides")
        XCTAssertGreaterThanOrEqual(session.audibleDuration, BlatherTimeline.openingBuffer)
        XCTAssertTrue(session.isPlaying)
        XCTAssertFalse(session.isGenerating)
        let firstPlaying = playback.updates.first { $0.playing }
        let startedAt = firstPlaying?.segments.reduce(0.0) { $0 + $1.duration } ?? 0
        XCTAssertGreaterThanOrEqual(startedAt, BlatherTimeline.openingBuffer)
        XCTAssertTrue(playback.updates.contains { update in
            !update.playing && update.segments.reduce(0.0) { $0 + $1.duration } < BlatherTimeline.openingBuffer
        })
    }

    func testFasterPlaybackBuffersMoreListeningTime() async {
        let playback = FakePlayback()
        let session = makeSession(
            narrator: FakeNarrator(text: "Hi."),
            synthesizer: FakeSynthesizer(duration: 15),
            playback: playback
        )
        session.setSpeed(.x2)

        await session.start(topic: "gears")
        let target = BlatherTimeline.openingBuffer * 2
        XCTAssertGreaterThanOrEqual(session.audibleDuration, target)
        let firstPlaying = playback.updates.first { $0.playing }
        let startedAt = firstPlaying?.segments.reduce(0.0) { $0 + $1.duration } ?? 0
        XCTAssertGreaterThanOrEqual(startedAt, target)
        XCTAssertTrue(playback.updates.contains { update in
            !update.playing && update.segments.reduce(0.0) { $0 + $1.duration } < target
        })
    }

    func testNextPassageStartsWhileTheCurrentOneIsSynthesized() async {
        let synthesizer = FakeSynthesizer(duration: 15)
        synthesizer.pauses = 1
        let narrator = FakeNarrator(text: "Hi.")
        let session = makeSession(
            narrator: narrator,
            synthesizer: synthesizer,
            playback: FakePlayback()
        )
        let running = Task { await session.start(topic: "wind") }
        defer { synthesizer.resumeAll() }

        var sawOverlap = false
        for _ in 0..<100 {
            if narrator.prompts.count >= 2, synthesizer.inFlight > 0 {
                sawOverlap = true
                break
            }
            try? await Task.sleep(nanoseconds: 20_000_000)
        }
        synthesizer.resumeAll()
        await running.value
        XCTAssertTrue(sawOverlap)
    }

    func testRedirectCutsUnheardAudio() async throws {
        let narrator = FakeNarrator(text: manyWords())
        let synthesizer = FakeSynthesizer(duration: 40)
        let playback = FakePlayback()
        let store = BlatherStore(root: directory)
        let session = makeSession(
            narrator: narrator,
            synthesizer: synthesizer,
            playback: playback,
            store: store
        )

        await session.start(topic: "rivers")
        let original = try XCTUnwrap(session.episode?.segments.first)
        let originalURL = store.audioURL(episodeID: try XCTUnwrap(session.episode?.id), fileName: original.fileName)
        XCTAssertTrue(FileManager.default.fileExists(atPath: originalURL.path))

        session.pause()
        XCTAssertFalse(session.isPlaying)
        await session.redirect("talk about dams")
        let episode = try XCTUnwrap(session.episode)
        XCTAssertEqual(episode.directions, ["talk about dams"])
        XCTAssertEqual(episode.segments.count, 1)
        XCTAssertNotEqual(episode.segments[0].id, original.id)
        XCTAssertFalse(FileManager.default.fileExists(atPath: originalURL.path))
        XCTAssertTrue(session.isPlaying)
        XCTAssertTrue(narrator.prompts.last?.contains("dams") == true)
    }

    func testRedirectShortensTheCurrentSegment() async throws {
        let narrator = FakeNarrator(text: manyWords())
        let synthesizer = FakeSynthesizer(duration: 40)
        let session = makeSession(narrator: narrator, synthesizer: synthesizer, playback: FakePlayback())

        await session.start(topic: "bridges")
        let kept = try XCTUnwrap(session.episode?.segments.first)
        session.pause()
        session.skip(by: 15)
        XCTAssertEqual(session.playhead, 15)
        session.skip(by: -10)
        XCTAssertEqual(session.playhead, 5)
        await session.redirect("steel, not stone")
        let episode = try XCTUnwrap(session.episode)
        XCTAssertEqual(episode.segments.count, 2)
        XCTAssertEqual(episode.segments[0].id, kept.id)
        XCTAssertEqual(episode.segments[0].duration, 5)
        XCTAssertEqual(session.playhead, 5, accuracy: 0.001)
    }

    func testContextWindowRetriesOnce() async throws {
        let speech = manyWords()
        let narrator = FakeNarrator(results: [
            .failure(BlatherNarrationError.contextExceeded),
            .success(BlatherNarration(text: speech, totalTokenCount: nil)),
        ])
        let session = makeSession(
            narrator: narrator,
            synthesizer: FakeSynthesizer(duration: 40),
            playback: FakePlayback()
        )
        await session.start(topic: "fog")
        XCTAssertTrue(session.didCompact)
        XCTAssertEqual(session.episode?.segments.first?.text, speech)
        XCTAssertEqual(narrator.freshSessions, [false, true])
        XCTAssertNil(session.errorMessage)
    }

    func testInterruptedModelCallRetriesOnce() async {
        let narrator = FakeNarrator(results: [
            .failure(BlatherNarrationError.interrupted),
            .success(BlatherNarration(text: manyWords(), totalTokenCount: nil)),
        ])
        let session = makeSession(
            narrator: narrator,
            synthesizer: FakeSynthesizer(duration: 40),
            playback: FakePlayback()
        )
        await session.start(topic: "seams")
        XCTAssertEqual(session.episode?.segments.count, 1)
        XCTAssertNil(session.errorMessage)
        XCTAssertTrue(session.isPlaying)
        XCTAssertEqual(narrator.discarded, 1)
    }

    func testRepeatedInterruptionSurfacesAPlainError() async {
        let narrator = FakeNarrator(results: [
            .failure(BlatherNarrationError.interrupted),
            .failure(BlatherNarrationError.interrupted),
        ])
        let session = makeSession(
            narrator: narrator,
            synthesizer: FakeSynthesizer(duration: 40),
            playback: FakePlayback()
        )
        await session.start(topic: "seams")
        XCTAssertEqual(session.episode?.segments.count, 0)
        XCTAssertEqual(session.errorMessage, "Writing paused. Try again.")
        XCTAssertFalse(session.errorMessage?.contains("error -1") == true)
        XCTAssertFalse(session.isPlaying)
    }

    func testForegroundContinuesAfterBackgroundExpiration() async {
        let synthesizer = FakeSynthesizer(duration: 40)
        synthesizer.pauses = 1
        let narrator = FakeNarrator(text: manyWords())
        let session = makeSession(
            narrator: narrator,
            synthesizer: synthesizer,
            playback: FakePlayback()
        )
        let running = Task { await session.start(topic: "hems") }
        defer { synthesizer.resumeAll() }
        for _ in 0..<100 {
            if synthesizer.inFlight > 0 { break }
            try? await Task.sleep(nanoseconds: 20_000_000)
        }
        session.interruptForBackground()
        synthesizer.pauses = 0
        synthesizer.resumeAll()
        await running.value
        XCTAssertNil(session.errorMessage)
        XCTAssertEqual(session.episode?.segments.count, 0)

        await session.sceneBecameActive()
        XCTAssertNil(session.errorMessage)
        XCTAssertEqual(session.episode?.segments.count, 1)
        XCTAssertTrue(session.isPlaying)
        XCTAssertFalse(session.isGenerating)
    }

    func testEmptySpeechSurfacesAnError() async {
        let narrator = FakeNarrator(text: "```\n# \n```")
        let session = makeSession(
            narrator: narrator,
            synthesizer: FakeSynthesizer(duration: 40),
            playback: FakePlayback()
        )
        await session.start(topic: "dust")
        XCTAssertEqual(session.episode?.segments.count, 0)
        XCTAssertEqual(session.errorMessage, "The model returned nothing to say.")
        XCTAssertFalse(session.isPlaying)
    }

    func testFillStopsAtTheSegmentCap() async {
        let session = makeSession(
            narrator: FakeNarrator(text: "Short."),
            synthesizer: FakeSynthesizer(duration: 1),
            playback: FakePlayback()
        )
        await session.start(topic: "bees")
        XCTAssertEqual(session.episode?.segments.count, BlatherTimeline.maxSegmentsPerFill)
        XCTAssertFalse(session.isGenerating)
    }

    func testBlankTopicIsIgnored() async {
        let session = makeSession(
            narrator: FakeNarrator(text: "Nope."),
            synthesizer: FakeSynthesizer(duration: 40),
            playback: FakePlayback()
        )
        await session.start(topic: "   ")
        XCTAssertEqual(session.mode, .idle)
        XCTAssertNil(session.episode)
    }

    func testFinishReplayContinueAndDelete() async throws {
        let narrator = FakeNarrator(text: manyWords())
        let playback = FakePlayback()
        let store = BlatherStore(root: directory)
        let session = makeSession(
            narrator: narrator,
            synthesizer: FakeSynthesizer(duration: 40),
            playback: playback,
            store: store
        )
        await session.start(topic: "owls")
        let id = try XCTUnwrap(session.episode?.id)

        session.finish()
        XCTAssertEqual(session.mode, .idle)
        XCTAssertNil(session.episode)
        XCTAssertNotNil(store.load(id: id))
        XCTAssertEqual(session.saved.map(\.id), [id])

        session.replay(id: id)
        XCTAssertEqual(session.mode, .replay)
        XCTAssertFalse(session.isPlaying)
        XCTAssertEqual(session.playhead, 0)
        XCTAssertEqual(session.episode?.segments.count, 1)

        let updatesBeforeExtend = playback.updates.count
        session.setExtending(true)
        await waitUntil { (session.episode?.segments.count ?? 0) > 1 }
        XCTAssertGreaterThan(session.episode?.segments.count ?? 0, 1)
        XCTAssertEqual(session.mode, .replay)
        XCTAssertFalse(session.isPlaying)
        XCTAssertEqual(session.playhead, 0)
        XCTAssertFalse(playback.updates.dropFirst(updatesBeforeExtend).contains { $0.playing })

        session.setExtending(false)
        await session.waitForFill()
        XCTAssertFalse(session.isExtending)
        XCTAssertTrue(session.generationHeld)
        XCTAssertFalse(session.isPlaying)

        session.resume()
        XCTAssertTrue(session.isPlaying)
        XCTAssertEqual(session.playhead, 0)

        session.delete(id: id)
        XCTAssertEqual(session.mode, .idle)
        XCTAssertNil(store.load(id: id))
        XCTAssertTrue(session.saved.isEmpty)
    }

    func testShutdownStopsPlayback() async {
        let playback = FakePlayback()
        let session = makeSession(
            narrator: FakeNarrator(text: "Hello."),
            synthesizer: FakeSynthesizer(duration: 40),
            playback: playback
        )
        await session.start(topic: "echoes")
        session.shutdown()
        XCTAssertTrue(playback.stopped)
        XCTAssertFalse(session.isPlaying)
    }

    private func waitUntil(attempts: Int = 50, _ predicate: () -> Bool) async {
        for _ in 0..<attempts where !predicate() {
            await Task.yield()
        }
    }

    private func makeSession(
        narrator: FakeNarrator,
        synthesizer: FakeSynthesizer,
        playback: FakePlayback,
        store: BlatherStore? = nil
    ) -> BlatherSession {
        BlatherSession(
            narrator: narrator,
            synthesizer: synthesizer,
            store: store ?? BlatherStore(root: directory),
            playback: playback,
            remote: BlatherRemoteControl()
        )
    }

    func testHeadphoneUnplugDoesNotResume() async {
        let playback = FakePlayback()
        let session = makeSession(
            narrator: FakeNarrator(text: "Still talking."),
            synthesizer: FakeSynthesizer(duration: 30),
            playback: playback
        )
        await session.start(topic: "cables")
        playback.onInterruption?(true, false)
        XCTAssertFalse(session.isPlaying)
        playback.onRouteLost?()
        playback.onInterruption?(false, true)
        XCTAssertFalse(session.isPlaying)
    }

    func testSpeedLabels() {
        XCTAssertEqual(BlatherSpeed.allCases.map(\.label), ["1×", "1.5×", "1.75×", "2×"])
        XCTAssertEqual(BlatherSpeed.nearest(1.6), .x1_5)
        XCTAssertEqual(BlatherSpeed.nearest(1.8), .x1_75)
        XCTAssertEqual(BlatherSpeed.nearest(1.9), .x2)
    }

    func testVoicePrefersConversationalOverCompact() {
        let samantha = BlatherVoice.make(
            identifier: "com.apple.voice.compact.en-US.Samantha",
            name: "Samantha",
            language: "en-US"
        )
        let ava = BlatherVoice.make(
            identifier: "com.apple.voice.super-compact.en-US.Ava",
            name: "Ava",
            language: "en-US"
        )
        let nora = BlatherVoice.make(
            identifier: "com.apple.ttsbundle.siri_Nora_en-US_premium",
            name: "Nora",
            language: "en-US",
            quality: .premium
        )
        let rocko = BlatherVoice.make(
            identifier: "com.apple.eloquence.en-US.Rocko",
            name: "Rocko",
            language: "en-US"
        )
        let daniel = BlatherVoice.make(
            identifier: "com.apple.voice.premium.en-GB.Daniel",
            name: "Daniel",
            language: "en-GB",
            quality: .premium
        )
        XCTAssertEqual(samantha.tone, .compact)
        XCTAssertEqual(ava.tone, .natural)
        XCTAssertEqual(nora.tone, .conversational)
        XCTAssertEqual(rocko.tone, .compact)
        XCTAssertEqual(daniel.tone, .premium)

        let choices = BlatherVoice.choices([samantha, ava, nora, rocko, daniel])
        XCTAssertEqual(choices.map(\.name), ["Nora", "Daniel", "Ava", "Samantha"])
        XCTAssertEqual(BlatherVoice.select(stored: nil, from: choices)?.name, "Nora")
        XCTAssertEqual(BlatherVoice.select(stored: ava.identifier, from: choices)?.name, "Ava")
        XCTAssertEqual(BlatherVoice.select(stored: "missing", from: choices)?.name, "Nora")
        let installed = BlatherVoice.choices([samantha, ava, rocko])
        XCTAssertEqual(BlatherVoice.select(stored: nil, from: installed)?.name, "Ava")
    }

    func testSelectedVoiceIsUsedForLaterSpeech() async {
        let compact = BlatherVoice.make(
            identifier: "com.apple.voice.compact.en-US.Samantha",
            name: "Samantha",
            language: "en-US"
        )
        let nora = BlatherVoice.make(
            identifier: "com.apple.ttsbundle.siri_Nora_en-US_premium",
            name: "Nora",
            language: "en-US",
            quality: .premium
        )
        let suite = "blather.voice.tests.\(UUID().uuidString)"
        let defaults = UserDefaults(suiteName: suite)!
        defer { defaults.removePersistentDomain(forName: suite) }
        let synthesizer = FakeSynthesizer(duration: 40)
        let session = BlatherSession(
            narrator: FakeNarrator(text: "Hello there."),
            synthesizer: synthesizer,
            store: BlatherStore(root: directory),
            playback: FakePlayback(),
            remote: BlatherRemoteControl(),
            voiceCatalog: { BlatherVoice.choices([compact, nora]) },
            defaults: defaults
        )
        XCTAssertEqual(session.voice?.identifier, nora.identifier)

        session.setVoice(identifier: compact.identifier)
        XCTAssertEqual(defaults.string(forKey: BlatherSession.voiceDefaultsKey), compact.identifier)
        await session.start(topic: "voices")
        XCTAssertEqual(synthesizer.voicesUsed.first, compact.identifier)

        let restored = BlatherSession(
            narrator: FakeNarrator(text: "Hello there."),
            synthesizer: FakeSynthesizer(duration: 40),
            store: BlatherStore(root: directory),
            playback: FakePlayback(),
            remote: BlatherRemoteControl(),
            voiceCatalog: { BlatherVoice.choices([compact, nora]) },
            defaults: defaults
        )
        XCTAssertEqual(restored.voice?.identifier, compact.identifier)
    }

    private func colorGrid(_ image: UIImage) -> [UInt32] {
        guard let cg = image.cgImage,
              let data = cg.dataProvider?.data,
              let bytes = CFDataGetBytePtr(data) else {
            return []
        }
        let bytesPerPixel = max(1, cg.bitsPerPixel / 8)
        let length = CFDataGetLength(data)
        let step = max(1, cg.width / 8)
        var colors: [UInt32] = []
        for y in stride(from: 0, to: cg.height, by: step) {
            for x in stride(from: 0, to: cg.width, by: step) {
                let offset = y * cg.bytesPerRow + x * bytesPerPixel
                guard offset + 3 < length else { continue }
                let packed = UInt32(bytes[offset]) << 16 | UInt32(bytes[offset + 1]) << 8 | UInt32(bytes[offset + 2])
                colors.append(packed)
            }
        }
        return colors
    }

    private func manyWords() -> String {
        String(repeating: "word ", count: 150).trimmingCharacters(in: .whitespaces)
    }

    private func segment(text: String, duration: TimeInterval, fileName: String) -> BlatherSegment {
        BlatherSegment(id: UUID(), text: text, fileName: fileName, duration: duration)
    }
}

@MainActor
private final class FakeNarrator: BlatherNarrator {
    var prompts: [String] = []
    var freshSessions: [Bool] = []
    private var results: [Result<BlatherNarration, Error>]

    init(text: String) {
        results = [.success(BlatherNarration(text: text, totalTokenCount: nil))]
    }

    init(results: [Result<BlatherNarration, Error>]) {
        self.results = results
    }

    private(set) var discarded = 0

    func prepare() {}

    func discardSession() {
        discarded += 1
    }

    func narrate(prompt: String, freshSession: Bool) async throws -> BlatherNarration {
        prompts.append(prompt)
        freshSessions.append(freshSession)
        let next = results.isEmpty
            ? .success(BlatherNarration(text: "Another sentence.", totalTokenCount: nil))
            : results.removeFirst()
        return try next.get()
    }
}

@MainActor
private final class FakeSynthesizer: BlatherSynthesizer {
    var duration: TimeInterval
    var pauses = 0
    private(set) var inFlight = 0
    private var waiters: [CheckedContinuation<Void, Never>] = []

    init(duration: TimeInterval) {
        self.duration = duration
    }

    var voiceIdentifier: String?
    private(set) var voicesUsed: [String?] = []

    func synthesize(_ text: String, to fileURL: URL) async throws -> TimeInterval {
        voicesUsed.append(voiceIdentifier)
        inFlight += 1
        defer { inFlight -= 1 }
        if pauses > 0 {
            pauses -= 1
            await withTaskCancellationHandler {
                await withCheckedContinuation { waiters.append($0) }
            } onCancel: {
                Task { @MainActor in
                    self.resumeAll()
                }
            }
            try Task.checkCancellation()
        }
        try FileManager.default.createDirectory(
            at: fileURL.deletingLastPathComponent(),
            withIntermediateDirectories: true
        )
        try Data(text.utf8).write(to: fileURL)
        return duration
    }

    func resumeAll() {
        let pending = waiters
        waiters.removeAll()
        for waiter in pending {
            waiter.resume()
        }
    }
}

@MainActor
private final class FakePlayback: BlatherPlaybackControlling {
    var onPlayhead: ((TimeInterval) -> Void)?
    var onEnded: (() -> Void)?
    var onInterruption: ((Bool, Bool) -> Void)?
    var onRouteLost: (() -> Void)?
    var updates: [(segments: [BlatherPlayable], playhead: TimeInterval, playing: Bool, rate: Double)] = []
    var stopped = false

    func update(segments: [BlatherPlayable], playhead: TimeInterval, playing: Bool, rate: Double) {
        updates.append((segments, playhead, playing, rate))
    }

    func stop() {
        stopped = true
    }
}
