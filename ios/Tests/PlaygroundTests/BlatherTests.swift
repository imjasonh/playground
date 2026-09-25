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
        let narrator = FakeNarrator(text: "The ice moves slowly.")
        let synthesizer = FakeSynthesizer(duration: 40)
        let playback = FakePlayback()
        let session = makeSession(narrator: narrator, synthesizer: synthesizer, playback: playback)

        await session.start(topic: "  glaciers  ")
        XCTAssertEqual(session.mode, .live)
        XCTAssertEqual(session.episode?.topic, "glaciers")
        XCTAssertEqual(session.episode?.segments.count, 1)
        XCTAssertEqual(session.episode?.segments.first?.text, "The ice moves slowly.")
        XCTAssertEqual(session.episode?.segments.first?.duration, 40)
        XCTAssertTrue(session.isPlaying)
        XCTAssertFalse(session.isGenerating)
        XCTAssertEqual(narrator.prompts.count, 1)
        XCTAssertTrue(narrator.prompts[0].contains("glaciers"))
        XCTAssertEqual(playback.updates.last?.playing, true as Bool?)
        XCTAssertEqual(session.saved.count, 1)

        session.skip(by: 20)
        await session.waitForFill()
        XCTAssertEqual(session.playhead, 20)
        XCTAssertEqual(session.episode?.segments.count, 2)
        XCTAssertEqual(narrator.prompts.count, 2)
        XCTAssertTrue(narrator.prompts[1].contains("Continue the explainer"))
        XCTAssertEqual(session.audibleDuration, 80)
    }

    func testRedirectCutsUnheardAudio() async throws {
        let narrator = FakeNarrator(text: "First passage.")
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
        let narrator = FakeNarrator(text: "Keep the start.")
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
        let narrator = FakeNarrator(results: [
            .failure(BlatherNarrationError.contextExceeded),
            .success(BlatherNarration(text: "Recovered sentence.", totalTokenCount: nil)),
        ])
        let session = makeSession(
            narrator: narrator,
            synthesizer: FakeSynthesizer(duration: 40),
            playback: FakePlayback()
        )
        await session.start(topic: "fog")
        XCTAssertTrue(session.didCompact)
        XCTAssertEqual(session.episode?.segments.first?.text, "Recovered sentence.")
        XCTAssertEqual(narrator.freshSessions, [false, true])
        XCTAssertNil(session.errorMessage)
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
        let narrator = FakeNarrator(text: "Saved line.")
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

        await session.continueTalking()
        XCTAssertEqual(session.mode, .live)
        XCTAssertTrue(session.isPlaying)
        XCTAssertEqual(session.episode?.segments.count, 1)

        session.skip(by: 20)
        await session.waitForFill()
        XCTAssertEqual(session.episode?.segments.count, 2)

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
            playback: playback
        )
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

    func prepare() {}

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

    init(duration: TimeInterval) {
        self.duration = duration
    }

    func synthesize(_ text: String, to fileURL: URL) async throws -> TimeInterval {
        try FileManager.default.createDirectory(
            at: fileURL.deletingLastPathComponent(),
            withIntermediateDirectories: true
        )
        try Data(text.utf8).write(to: fileURL)
        return duration
    }
}

@MainActor
private final class FakePlayback: BlatherPlaybackControlling {
    var onPlayhead: ((TimeInterval) -> Void)?
    var onEnded: (() -> Void)?
    var onInterruption: ((Bool, Bool) -> Void)?
    var updates: [(segments: [BlatherPlayable], playhead: TimeInterval, playing: Bool)] = []
    var stopped = false

    func update(segments: [BlatherPlayable], playhead: TimeInterval, playing: Bool) {
        updates.append((segments, playhead, playing))
    }

    func stop() {
        stopped = true
    }
}
