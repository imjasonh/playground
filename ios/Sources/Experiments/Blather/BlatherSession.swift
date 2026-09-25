import AVFoundation
import Foundation
import MediaPlayer
import UIKit

/// Text returned by the narrator. `totalTokenCount` is the model session's
/// measured total when the on-device model reports one.
struct BlatherNarration: Equatable {
    var text: String
    var totalTokenCount: Int?
}

enum BlatherNarrationError: Error, Equatable {
    case contextExceeded
    case modelUnavailable(String)
    case failed(String)
}

/// Writes the next spoken passage. Tests substitute a fake.
@MainActor
protocol BlatherNarrator: AnyObject {
    func prepare()
    func narrate(prompt: String, freshSession: Bool) async throws -> BlatherNarration
}

/// Renders speech to a file without playing it. Tests substitute a fake.
@MainActor
protocol BlatherSynthesizer: AnyObject {
    func synthesize(_ text: String, to fileURL: URL) async throws -> TimeInterval
}

/// Plays the episode timeline. The session owns play, pause, seek, and speed.
@MainActor
protocol BlatherPlaybackControlling: AnyObject {
    var onPlayhead: ((TimeInterval) -> Void)? { get set }
    var onEnded: (() -> Void)? { get set }
    var onInterruption: ((Bool, Bool) -> Void)? { get set }
    var onRouteLost: (() -> Void)? { get set }
    func update(segments: [BlatherPlayable], playhead: TimeInterval, playing: Bool, rate: Double)
    func stop()
}

/// Lock-screen play, pause, 10-second skip, and playback speed.
@MainActor
final class BlatherRemoteControl {
    enum Command {
        case play
        case pause
        case toggle
        case skipForward
        case skipBackward
        case setRate(Double)
    }

    private var tokens: [(MPRemoteCommand, Any)] = []

    func attach(handler: @escaping @MainActor (Command) -> Void) {
        detach()
        let center = MPRemoteCommandCenter.shared()
        center.skipForwardCommand.preferredIntervals = [NSNumber(value: BlatherTimeline.skipStep)]
        center.skipBackwardCommand.preferredIntervals = [NSNumber(value: BlatherTimeline.skipStep)]
        center.playCommand.isEnabled = true
        center.pauseCommand.isEnabled = true
        center.togglePlayPauseCommand.isEnabled = true
        center.skipForwardCommand.isEnabled = true
        center.skipBackwardCommand.isEnabled = true
        center.changePlaybackRateCommand.isEnabled = true
        center.changePlaybackRateCommand.supportedPlaybackRates = BlatherSpeed.allCases.map {
            NSNumber(value: $0.rawValue)
        }
        tokens = [
            token(center.playCommand, command: .play, handler: handler),
            token(center.pauseCommand, command: .pause, handler: handler),
            token(center.togglePlayPauseCommand, command: .toggle, handler: handler),
            token(center.skipForwardCommand, command: .skipForward, handler: handler),
            token(center.skipBackwardCommand, command: .skipBackward, handler: handler),
        ]
        let rateToken = center.changePlaybackRateCommand.addTarget { event in
            let rate = (event as? MPChangePlaybackRateCommandEvent)?.playbackRate ?? 1
            Task { @MainActor in
                handler(.setRate(Double(rate)))
            }
            return .success
        }
        tokens.append((center.changePlaybackRateCommand, rateToken))
    }

    private func token(
        _ command: MPRemoteCommand,
        command kind: Command,
        handler: @escaping @MainActor (Command) -> Void
    ) -> (MPRemoteCommand, Any) {
        let token = command.addTarget { _ in
            Task { @MainActor in
                handler(kind)
            }
            return .success
        }
        return (command, token)
    }

    func detach() {
        for (command, token) in tokens {
            command.removeTarget(token)
        }
        tokens = []
        let center = MPRemoteCommandCenter.shared()
        center.playCommand.isEnabled = false
        center.pauseCommand.isEnabled = false
        center.togglePlayPauseCommand.isEnabled = false
        center.skipForwardCommand.isEnabled = false
        center.skipBackwardCommand.isEnabled = false
        center.changePlaybackRateCommand.isEnabled = false
    }
}

/// Drives generation, speech files, playback, and the saved-audio library.
@MainActor
final class BlatherSession: ObservableObject {
    enum Mode: Equatable {
        case idle
        case live
        case replay
    }

    @Published private(set) var mode: Mode = .idle
    @Published private(set) var episode: BlatherEpisode?
    @Published private(set) var playhead: TimeInterval = 0
    @Published private(set) var isPlaying = false
    @Published private(set) var isGenerating = false
    @Published private(set) var errorMessage: String?
    @Published private(set) var didCompact = false
    @Published private(set) var saved: [BlatherEpisodeSummary] = []
    @Published private(set) var speed: BlatherSpeed = .x1
    @Published private(set) var modelGate: AgentModelGate

    private let narrator: any BlatherNarrator
    private let synthesizer: any BlatherSynthesizer
    private let store: BlatherStore
    private let playback: any BlatherPlaybackControlling
    private let remote: BlatherRemoteControl
    private let gateProvider: () -> AgentModelGate

    private var planner = BlatherPlanner()
    private var generation = 0
    private var fillRunning = false
    private var wantsAutoplay = false
    private var generationFailed = false
    private var resumeAfterInterruption = false
    private var chain: Task<Void, Never>?
    /// JPEG bytes for the lock screen. `Data` can cross the artwork callback,
    /// which may run off the main actor. `UIImage` cannot.
    private var nowPlayingCover: (id: UUID, data: Data, size: CGSize)?

    init(
        narrator: any BlatherNarrator,
        synthesizer: any BlatherSynthesizer,
        store: BlatherStore,
        playback: any BlatherPlaybackControlling,
        remote: BlatherRemoteControl,
        modelGate: AgentModelGate = .available,
        gateProvider: @escaping () -> AgentModelGate = { .available }
    ) {
        self.narrator = narrator
        self.synthesizer = synthesizer
        self.store = store
        self.playback = playback
        self.remote = remote
        self.modelGate = modelGate
        self.gateProvider = gateProvider
        playback.onPlayhead = { [weak self] time in
            MainActor.assumeIsolated {
                self?.notePlayhead(time)
            }
        }
        playback.onEnded = { [weak self] in
            MainActor.assumeIsolated {
                self?.playbackEnded()
            }
        }
        playback.onInterruption = { [weak self] began, shouldResume in
            MainActor.assumeIsolated {
                self?.handleInterruption(began: began, shouldResume: shouldResume)
            }
        }
        playback.onRouteLost = { [weak self] in
            MainActor.assumeIsolated {
                self?.pauseForRouteLoss()
            }
        }
    }

    static func live() -> BlatherSession {
        BlatherSession(
            narrator: BlatherOnDeviceNarrator(),
            synthesizer: BlatherSpeechRenderer(),
            store: BlatherStore.applicationSupport(),
            playback: BlatherAVPlayback(),
            remote: BlatherRemoteControl(),
            modelGate: BlatherAvailability.current(),
            gateProvider: { BlatherAvailability.current() }
        )
    }

    var audibleDuration: TimeInterval {
        guard let episode else { return 0 }
        return BlatherTimeline.duration(of: episode.segments)
    }

    var hasAudio: Bool { audibleDuration > 0.05 }

    var currentSegmentIndex: Int? {
        guard let episode, !episode.segments.isEmpty else { return nil }
        return BlatherTimeline.locate(playhead, durations: episode.segments.map(\.duration)).index
    }

    func coverURL(for id: UUID) -> URL {
        store.coverURL(episodeID: id)
    }

    func refresh() {
        modelGate = gateProvider()
        ensureCovers()
        saved = store.summaries()
        narrator.prepare()
        remote.attach { [weak self] command in
            guard let self else { return }
            switch command {
            case .play:
                self.resume()
            case .pause:
                self.pause()
            case .toggle:
                if self.isPlaying {
                    self.pause()
                } else {
                    self.resume()
                }
            case .skipForward:
                self.skip(by: BlatherTimeline.skipStep)
            case .skipBackward:
                self.skip(by: -BlatherTimeline.skipStep)
            case .setRate(let rate):
                self.setSpeed(BlatherSpeed.nearest(rate))
            }
        }
    }

    func setSpeed(_ speed: BlatherSpeed) {
        guard speed != self.speed else { return }
        self.speed = speed
        syncPlayback()
        scheduleFill()
    }

    func performModelGateAction(_ action: AgentModelGateAction) async {
        switch action {
        case .openAppleIntelligenceSettings:
            await AgentAppleIntelligenceSettings.open()
        case .checkAgain:
            refresh()
        }
    }

    func start(topic raw: String) async {
        let topic = Self.storedTopic(raw)
        guard !topic.isEmpty else { return }
        generation &+= 1
        let token = generation
        let now = Date()
        let created = BlatherEpisode(
            id: UUID(),
            topic: topic,
            createdAt: now,
            updatedAt: now,
            directions: [],
            segments: []
        )
        planner = BlatherPlanner()
        fillRunning = true
        persist(created)
        writeCover(topic: topic, episodeID: created.id)
        episode = created
        mode = .live
        playhead = 0
        isPlaying = false
        wantsAutoplay = true
        errorMessage = nil
        generationFailed = false
        didCompact = false
        syncPlayback()
        await runFill(token: token, after: chain)
    }

    func pause() {
        guard mode == .live || mode == .replay else { return }
        isPlaying = false
        wantsAutoplay = false
        syncPlayback()
    }

    func resume() {
        guard hasAudio, mode == .live || mode == .replay else { return }
        wantsAutoplay = mode == .live
        isPlaying = true
        syncPlayback()
        if mode == .live {
            scheduleFill()
        }
    }

    func skip(by delta: TimeInterval) {
        seek(to: playhead + delta)
    }

    func seek(to time: TimeInterval) {
        guard hasAudio else { return }
        playhead = BlatherTimeline.clamped(time, duration: audibleDuration)
        syncPlayback()
        if isPlaying, mode == .live {
            scheduleFill()
        }
    }

    func redirect(_ raw: String) async {
        let text = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !text.isEmpty, var current = episode, mode == .live || mode == .replay else { return }
        generation &+= 1
        let token = generation
        fillRunning = true
        let previous = chain
        let cut = BlatherTimeline.cut(segments: current.segments, at: playhead)
        current.segments = cut.segments
        current.directions.append(String(text.prefix(500)))
        current.updatedAt = Date()
        episode = current
        playhead = cut.playhead
        mode = .live
        wantsAutoplay = true
        isPlaying = false
        errorMessage = nil
        generationFailed = false
        if persist(current) {
            for name in cut.removedFileNames {
                store.removeAudio(episodeID: current.id, fileName: name)
            }
        }
        syncPlayback()
        await runFill(token: token, after: previous)
    }

    func continueTalking() async {
        guard mode == .replay || mode == .live else { return }
        guard modelGate.isAvailable else { return }
        mode = .live
        wantsAutoplay = true
        generationFailed = false
        errorMessage = nil
        if hasAudio {
            isPlaying = true
            syncPlayback()
        }
        guard !hasAudio || shouldPrefetch(playhead: playhead, duration: audibleDuration) else {
            return
        }
        generation &+= 1
        let token = generation
        fillRunning = true
        await runFill(token: token, after: chain)
    }

    func retry() async {
        guard mode == .live || mode == .replay else { return }
        generationFailed = false
        errorMessage = nil
        mode = .live
        wantsAutoplay = true
        generation &+= 1
        let token = generation
        fillRunning = true
        await runFill(token: token, after: chain)
    }

    func replay(id: UUID) {
        guard let loaded = store.load(id: id) else { return }
        generation &+= 1
        chain?.cancel()
        episode = loaded
        mode = .replay
        isPlaying = false
        wantsAutoplay = false
        playhead = 0
        errorMessage = nil
        generationFailed = false
        didCompact = false
        isGenerating = false
        fillRunning = false
        seedPlanner(with: loaded)
        syncPlayback()
    }

    func delete(id: UUID) {
        store.delete(id: id)
        if episode?.id == id {
            finish()
        } else {
            saved = store.summaries()
        }
    }

    /// Keeps the episode on disk and returns to the topic field.
    func finish() {
        generation &+= 1
        chain?.cancel()
        mode = .idle
        episode = nil
        isPlaying = false
        wantsAutoplay = false
        isGenerating = false
        fillRunning = false
        playhead = 0
        errorMessage = nil
        generationFailed = false
        didCompact = false
        planner = BlatherPlanner()
        playback.update(segments: [], playhead: 0, playing: false, rate: speed.rawValue)
        publishNowPlaying()
        deactivateAudio()
        saved = store.summaries()
    }

    /// Stops audio and lock-screen commands when the experiment closes.
    func shutdown() {
        generation &+= 1
        chain?.cancel()
        isPlaying = false
        wantsAutoplay = false
        isGenerating = false
        fillRunning = false
        playback.stop()
        remote.detach()
        MPNowPlayingInfoCenter.default().nowPlayingInfo = nil
        deactivateAudio()
    }

    /// Waits for the fill scheduled by the latest playhead or transport change.
    func waitForFill() async {
        await chain?.value
    }

    private func notePlayhead(_ time: TimeInterval) {
        playhead = BlatherTimeline.clamped(time, duration: audibleDuration)
        guard mode == .live, isPlaying else { return }
        scheduleFill()
    }

    private func playbackEnded() {
        guard !isGenerating else {
            publishNowPlaying()
            return
        }
        guard mode != .live || !shouldPrefetch(playhead: playhead, duration: audibleDuration) else {
            publishNowPlaying()
            return
        }
        isPlaying = false
        wantsAutoplay = false
        publishNowPlaying()
    }

    private func handleInterruption(began: Bool, shouldResume: Bool) {
        if began {
            resumeAfterInterruption = isPlaying
            if isPlaying {
                pause()
            }
            return
        }
        if shouldResume, resumeAfterInterruption {
            resume()
        }
        resumeAfterInterruption = false
    }

    /// Headphones unplugged. Pause, and do not start playback on the speaker later.
    private func pauseForRouteLoss() {
        resumeAfterInterruption = false
        pause()
    }

    private func scheduleFill() {
        guard mode == .live, isPlaying, !fillRunning, !generationFailed else { return }
        guard shouldPrefetch(playhead: playhead, duration: audibleDuration) else { return }
        let token = generation
        fillRunning = true
        let previous = chain
        let task = Task { [weak self] in
            await previous?.value
            guard let self else { return }
            guard self.generation == token, self.mode == .live, self.isPlaying, !self.generationFailed else {
                if self.generation == token {
                    self.fillRunning = false
                }
                return
            }
            guard self.shouldPrefetch(playhead: self.playhead, duration: self.audibleDuration) else {
                self.fillRunning = false
                return
            }
            await self.fillAhead(token: token)
        }
        chain = task
    }

    private func runFill(token: Int, after previous: Task<Void, Never>?) async {
        let task = Task { [weak self] in
            await previous?.value
            guard let self, self.generation == token else { return }
            await self.fillAhead(token: token)
        }
        chain = task
        await task.value
    }

    private func fillAhead(token: Int) async {
        fillRunning = true
        isGenerating = true
        defer {
            if generation == token {
                isGenerating = false
                fillRunning = false
            }
        }
        var produced = 0
        while generation == token, !Task.isCancelled {
            if produced > 0 {
                guard mode == .live, !generationFailed else { return }
                guard shouldPrefetch(playhead: playhead, duration: audibleDuration) else { return }
            }
            if produced >= BlatherTimeline.maxSegmentsPerFill { return }
            let before = audibleDuration
            let wrote = await appendOne(token: token)
            if !wrote { return }
            produced += 1
            if audibleDuration <= before { return }
        }
    }

    private func appendOne(token: Int) async -> Bool {
        guard generation == token, let current = episode else { return false }
        let request = planner.makeRequest(
            topic: current.topic,
            directions: current.directions,
            spoken: current.segments.map(\.text)
        )
        if request.didCompact {
            didCompact = true
        }
        let narration: BlatherNarration
        let prompt: String
        do {
            let result = try await withBackgroundTime {
                try await self.narrate(request, token: token)
            }
            narration = result.narration
            prompt = result.prompt
        } catch {
            guard generation == token else { return false }
            if error is CancellationError {
                return false
            }
            fail(error)
            return false
        }
        guard generation == token else { return false }
        let speech = BlatherScript.clean(narration.text)
        guard !speech.isEmpty else {
            fail(BlatherNarrationError.failed("The model returned nothing to say."))
            return false
        }
        let segmentID = UUID()
        let fileName = "\(segmentID.uuidString).caf"
        let url = store.audioURL(episodeID: current.id, fileName: fileName)
        let duration: TimeInterval
        do {
            duration = try await synthesizer.synthesize(speech, to: url)
        } catch {
            store.removeAudio(episodeID: current.id, fileName: fileName)
            guard generation == token else { return false }
            fail(BlatherNarrationError.failed("Couldn't build the audio."))
            return false
        }
        guard generation == token else {
            store.removeAudio(episodeID: current.id, fileName: fileName)
            return false
        }
        guard duration >= 0.05 else {
            store.removeAudio(episodeID: current.id, fileName: fileName)
            fail(BlatherNarrationError.failed("Couldn't build the audio."))
            return false
        }
        guard var latest = episode, latest.id == current.id else {
            store.removeAudio(episodeID: current.id, fileName: fileName)
            return false
        }
        let segment = BlatherSegment(id: segmentID, text: speech, fileName: fileName, duration: duration)
        latest.segments.append(segment)
        latest.updatedAt = Date()
        episode = latest
        planner.commit(prompt: prompt, speech: speech, measuredTotalTokens: narration.totalTokenCount)
        if wantsAutoplay {
            isPlaying = true
        }
        persist(latest)
        syncPlayback()
        return true
    }

    private func narrate(
        _ request: BlatherNarrationRequest,
        token: Int
    ) async throws -> (narration: BlatherNarration, prompt: String) {
        do {
            let narration = try await narrator.narrate(prompt: request.prompt, freshSession: request.freshSession)
            return (narration, request.prompt)
        } catch {
            guard generation == token else { throw error }
            guard let narrationError = error as? BlatherNarrationError,
                  case .contextExceeded = narrationError else {
                throw error
            }
            planner.forceCompact()
            didCompact = true
            guard let current = episode else { throw error }
            let retry = planner.makeRequest(
                topic: current.topic,
                directions: current.directions,
                spoken: current.segments.map(\.text)
            )
            let narration = try await narrator.narrate(prompt: retry.prompt, freshSession: true)
            return (narration, retry.prompt)
        }
    }

    private func seedPlanner(with episode: BlatherEpisode) {
        planner = BlatherPlanner()
        for segment in episode.segments.suffix(3) {
            planner.noteSpoken(segment.text)
        }
    }

    @discardableResult
    private func persist(_ episode: BlatherEpisode) -> Bool {
        do {
            try store.save(episode)
            saved = store.summaries()
            return true
        } catch {
            errorMessage = "Couldn't save audio on this device."
            return false
        }
    }

    private func fail(_ error: Error) {
        generationFailed = true
        wantsAutoplay = false
        if !hasAudio || playhead >= audibleDuration - 0.05 {
            isPlaying = false
            syncPlayback()
        }
        if let narration = error as? BlatherNarrationError {
            switch narration {
            case .contextExceeded:
                errorMessage = "The model ran out of context. Try a new topic."
            case .modelUnavailable(let message):
                errorMessage = message
            case .failed(let message):
                errorMessage = message
            }
            return
        }
        errorMessage = "Couldn't write the next part."
    }

    private var playables: [BlatherPlayable] {
        guard let episode else { return [] }
        return episode.segments.map { segment in
            BlatherPlayable(
                url: store.audioURL(episodeID: episode.id, fileName: segment.fileName),
                duration: segment.duration
            )
        }
    }

    private func shouldPrefetch(playhead: TimeInterval, duration: TimeInterval) -> Bool {
        BlatherTimeline.shouldPrefetch(playhead: playhead, duration: duration, rate: speed.rawValue)
    }

    /// Zero while paused or waiting on the next file, so the lock screen clock stops.
    private var nowPlayingRate: Double {
        let caughtUp = !hasAudio || playhead >= audibleDuration - 0.05
        guard isPlaying, !caughtUp else { return 0 }
        return speed.rawValue
    }

    private func syncPlayback() {
        playback.update(segments: playables, playhead: playhead, playing: isPlaying && hasAudio, rate: speed.rawValue)
        publishNowPlaying()
    }

    private func publishNowPlaying() {
        guard mode != .idle, let episode, hasAudio else {
            MPNowPlayingInfoCenter.default().nowPlayingInfo = nil
            return
        }
        var info: [String: Any] = [
            MPMediaItemPropertyTitle: episode.topic,
            MPMediaItemPropertyArtist: "Blather",
            MPNowPlayingInfoPropertyElapsedPlaybackTime: playhead,
            MPMediaItemPropertyPlaybackDuration: audibleDuration,
            MPNowPlayingInfoPropertyPlaybackRate: nowPlayingRate,
        ]
        if let art = nowPlayingArtwork(for: episode) {
            let bytes = art.data
            info[MPMediaItemPropertyArtwork] = MPMediaItemArtwork(boundsSize: art.size) { _ in
                UIImage(data: bytes) ?? UIImage()
            }
        }
        MPNowPlayingInfoCenter.default().nowPlayingInfo = info
    }

    private func writeCover(topic: String, episodeID: UUID) {
        nowPlayingCover = nil
        try? store.saveCover(BlatherArtwork.jpeg(topic: topic), episodeID: episodeID)
    }

    private func ensureCovers() {
        for summary in store.summaries() where !store.hasCover(episodeID: summary.id) {
            try? store.saveCover(BlatherArtwork.jpeg(topic: summary.topic), episodeID: summary.id)
        }
    }

    private func nowPlayingArtwork(for episode: BlatherEpisode) -> (data: Data, size: CGSize)? {
        if nowPlayingCover?.id == episode.id, let cached = nowPlayingCover {
            return (cached.data, cached.size)
        }
        let url = store.coverURL(episodeID: episode.id)
        guard let data = try? Data(contentsOf: url), let image = UIImage(data: data) else {
            return nil
        }
        nowPlayingCover = (episode.id, data, image.size)
        return (data, image.size)
    }

    private func deactivateAudio() {
        try? AVAudioSession.sharedInstance().setActive(false, options: [.notifyOthersOnDeactivation])
    }

    private func withBackgroundTime<T>(_ body: () async throws -> T) async rethrows -> T {
        let token = BackgroundToken()
        token.begin()
        defer { token.end() }
        return try await body()
    }

    private static func storedTopic(_ raw: String) -> String {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard trimmed.count > 280 else { return trimmed }
        let end = trimmed.index(trimmed.startIndex, offsetBy: 280)
        return String(trimmed[..<end]).trimmingCharacters(in: .whitespacesAndNewlines)
    }
}

/// Ends a background task once, from either the expiration handler or `defer`.
@MainActor
private final class BackgroundToken {
    private var id: UIBackgroundTaskIdentifier = .invalid

    func begin() {
        guard id == .invalid else { return }
        // Unit tests run in the test bundle, which has no UIApplication.
        // Hosted in the app, this keeps a model call alive if the phone locks.
        guard Bundle.main.bundlePath.hasSuffix(".app") else { return }
        id = UIApplication.shared.beginBackgroundTask(withName: "Blather") { [weak self] in
            Task { @MainActor in
                self?.end()
            }
        }
    }

    func end() {
        let current = id
        id = .invalid
        guard current != .invalid else { return }
        UIApplication.shared.endBackgroundTask(current)
    }
}
