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
    /// The model session was dropped, usually because the app was backgrounded.
    case interrupted
}

/// Writes the next spoken passage. Tests substitute a fake.
@MainActor
protocol BlatherNarrator: AnyObject {
    func prepare()
    func discardSession()
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
    /// False until this episode has actually started. Resume stays held while
    /// the opening buffer is still filling.
    private var hasStartedPlayback = false
    private var generationFailed = false
    /// Set when a model call dies in the background. Opening the app continues it.
    private var resumeWhenActive = false
    private var interruptionAttempts = 0
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

    /// Model availability, plus continuing a passage that the background
    /// killed. Lock-screen play uses the same path.
    func sceneBecameActive() async {
        refresh()
        guard resumeWhenActive else { return }
        resumeWhenActive = false
        interruptionAttempts = 0
        await continueAfterInterruption()
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
        hasStartedPlayback = false
        errorMessage = nil
        generationFailed = false
        resumeWhenActive = false
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
        if resumeWhenActive {
            Task { await sceneBecameActive() }
            return
        }
        guard hasAudio, mode == .live || mode == .replay else { return }
        wantsAutoplay = mode == .live
        let holdingOpening = mode == .live
            && !hasStartedPlayback
            && !generationFailed
            && BlatherTimeline.needsOpeningAudio(
                playhead: playhead,
                duration: audibleDuration,
                rate: speed.rawValue
            )
        if !holdingOpening {
            isPlaying = true
            hasStartedPlayback = true
        }
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
        hasStartedPlayback = false
        errorMessage = nil
        generationFailed = false
        resumeWhenActive = false
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
        resumeWhenActive = false
        errorMessage = nil
        if hasAudio {
            isPlaying = true
            hasStartedPlayback = true
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
        resumeWhenActive = false
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
        hasStartedPlayback = false
        playhead = 0
        errorMessage = nil
        generationFailed = false
        resumeWhenActive = false
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
        hasStartedPlayback = false
        isGenerating = false
        fillRunning = false
        playhead = 0
        errorMessage = nil
        generationFailed = false
        resumeWhenActive = false
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
        resumeWhenActive = false
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
        let background = BackgroundToken()
        background.begin { [weak self] in
            self?.interruptForBackground()
        }
        defer {
            background.end()
        }
        defer {
            if generation == token {
                isGenerating = false
                fillRunning = false
                startPlayback(token: token, allowShort: true)
            }
        }
        var produced = 0
        var queued: DraftPassage?
        while generation == token, !Task.isCancelled {
            if produced > 0 {
                guard mode == .live, !generationFailed else { return }
                if !shouldContinueFill(produced: produced) {
                    await finishQueued(queued, token: token, produced: produced)
                    return
                }
            }
            if produced >= BlatherTimeline.maxSegmentsPerFill {
                await finishQueued(queued, token: token, produced: produced)
                return
            }

            let draft: DraftPassage
            if let queuedDraft = queued {
                queued = nil
                draft = queuedDraft
            } else if let prepared = await prepareDraft(token: token, pendingSpeech: nil) {
                draft = prepared
            } else {
                return
            }

            let projected = audibleDuration + BlatherTimeline.estimatedDuration(of: draft.speech)
            let overlap = produced + 1 < BlatherTimeline.maxSegmentsPerFill
                && shouldProjectMore(projectedDuration: projected)
            if overlap {
                planner.commit(
                    prompt: draft.prompt,
                    speech: draft.speech,
                    measuredTotalTokens: draft.totalTokenCount
                )
                let synthesis = Task { [weak self] () -> Bool in
                    guard let self else { return false }
                    return await self.finishDraft(draft, token: token, commit: false)
                }
                queued = await prepareDraft(token: token, pendingSpeech: draft.speech)
                let wrote = await synthesis.value
                guard wrote else { return }
                produced += 1
                startPlayback(token: token, allowShort: false)
                if queued == nil { return }
            } else {
                let before = audibleDuration
                let wrote = await finishDraft(draft, token: token, commit: true)
                guard wrote else { return }
                produced += 1
                if audibleDuration <= before { return }
                startPlayback(token: token, allowShort: false)
            }
        }
    }

    /// True when the audio on disk, plus this passage's estimated length, is
    /// still short of the opening buffer or the prefetch lead.
    private func shouldProjectMore(projectedDuration: TimeInterval) -> Bool {
        if !isPlaying {
            return BlatherTimeline.needsOpeningAudio(
                playhead: playhead,
                duration: projectedDuration,
                rate: speed.rawValue
            )
        }
        return shouldPrefetch(playhead: playhead, duration: projectedDuration)
    }

    /// The opening fill writes until about 40 seconds of listening time are
    /// ready. After playback starts, the fill stops once the prefetch lead
    /// is covered.
    private func shouldContinueFill(produced: Int) -> Bool {
        guard produced < BlatherTimeline.maxSegmentsPerFill else { return false }
        if !isPlaying, BlatherTimeline.needsOpeningAudio(
            playhead: playhead,
            duration: audibleDuration,
            rate: speed.rawValue
        ) {
            return true
        }
        return shouldPrefetch(playhead: playhead, duration: audibleDuration)
    }

    /// Starts playback once the opening buffer is ready. `allowShort` covers
    /// the segment cap, so a burst of very short clips still starts.
    private func startPlayback(token: Int, allowShort: Bool) {
        guard generation == token, wantsAutoplay, hasAudio, !isPlaying, !generationFailed else { return }
        if !allowShort, BlatherTimeline.needsOpeningAudio(
            playhead: playhead,
            duration: audibleDuration,
            rate: speed.rawValue
        ) {
            return
        }
        isPlaying = true
        hasStartedPlayback = true
        syncPlayback()
    }

    private struct DraftPassage {
        var episodeID: UUID
        var speech: String
        var prompt: String
        var totalTokenCount: Int?
        var segmentID: UUID
        var fileName: String
    }

    /// Writes a passage that was already narrated. Used when the buffer fills
    /// while the next model call is still in flight.
    private func finishQueued(_ draft: DraftPassage?, token: Int, produced: Int) async {
        guard let draft, produced < BlatherTimeline.maxSegmentsPerFill else { return }
        guard generation == token, mode == .live, !generationFailed else { return }
        let before = audibleDuration
        let wrote = await finishDraft(draft, token: token, commit: true)
        guard wrote, audibleDuration > before else { return }
        startPlayback(token: token, allowShort: false)
    }

    private func prepareDraft(token: Int, pendingSpeech: String?) async -> DraftPassage? {
        guard generation == token, let current = episode else { return nil }
        let request = planner.makeRequest(
            topic: current.topic,
            directions: current.directions,
            spoken: spokenLines(pending: pendingSpeech)
        )
        if request.didCompact {
            didCompact = true
        }
        let narration: BlatherNarration
        let prompt: String
        do {
            let result = try await withBackgroundTime {
                try await self.narrate(request, token: token, pendingSpeech: pendingSpeech)
            }
            narration = result.narration
            prompt = result.prompt
        } catch {
            guard generation == token else { return nil }
            if error is CancellationError || resumeWhenActive {
                return nil
            }
            if BlatherModelFailure.isInterrupted(error) {
                return await handleInterruption(token: token, pendingSpeech: pendingSpeech)
            }
            fail(error)
            return nil
        }
        guard generation == token, !resumeWhenActive else { return nil }
        interruptionAttempts = 0
        let speech = BlatherScript.clean(narration.text)
        guard !speech.isEmpty else {
            fail(BlatherNarrationError.failed("The model returned nothing to say."))
            return nil
        }
        let segmentID = UUID()
        return DraftPassage(
            episodeID: current.id,
            speech: speech,
            prompt: prompt,
            totalTokenCount: narration.totalTokenCount,
            segmentID: segmentID,
            fileName: "\(segmentID.uuidString).caf"
        )
    }

    private func finishDraft(_ draft: DraftPassage, token: Int, commit: Bool) async -> Bool {
        let url = store.audioURL(episodeID: draft.episodeID, fileName: draft.fileName)
        let duration: TimeInterval
        do {
            duration = try await synthesizer.synthesize(draft.speech, to: url)
        } catch {
            store.removeAudio(episodeID: draft.episodeID, fileName: draft.fileName)
            guard generation == token else { return false }
            fail(BlatherNarrationError.failed("Couldn't build the audio."))
            return false
        }
        guard generation == token else {
            store.removeAudio(episodeID: draft.episodeID, fileName: draft.fileName)
            return false
        }
        guard duration >= 0.05 else {
            store.removeAudio(episodeID: draft.episodeID, fileName: draft.fileName)
            fail(BlatherNarrationError.failed("Couldn't build the audio."))
            return false
        }
        guard var latest = episode, latest.id == draft.episodeID else {
            store.removeAudio(episodeID: draft.episodeID, fileName: draft.fileName)
            return false
        }
        let segment = BlatherSegment(
            id: draft.segmentID,
            text: draft.speech,
            fileName: draft.fileName,
            duration: duration
        )
        latest.segments.append(segment)
        latest.updatedAt = Date()
        episode = latest
        if commit {
            planner.commit(
                prompt: draft.prompt,
                speech: draft.speech,
                measuredTotalTokens: draft.totalTokenCount
            )
        }
        persist(latest)
        syncPlayback()
        return true
    }

    private func spokenLines(pending: String?) -> [String] {
        var lines = episode?.segments.map(\.text) ?? []
        if let pending {
            let trimmed = pending.trimmingCharacters(in: .whitespacesAndNewlines)
            if !trimmed.isEmpty {
                lines.append(trimmed)
            }
        }
        return lines
    }

    private func narrate(
        _ request: BlatherNarrationRequest,
        token: Int,
        pendingSpeech: String?
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
                spoken: spokenLines(pending: pendingSpeech)
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

    /// iOS is about to suspend the process. Drop the in-flight model call and
    /// continue it the next time the app is active.
    func interruptForBackground() {
        guard mode == .live, !resumeWhenActive else { return }
        resumeWhenActive = true
        generation &+= 1
        generationFailed = false
        errorMessage = nil
        isGenerating = false
        fillRunning = false
        chain?.cancel()
    }

    private func handleInterruption(token: Int, pendingSpeech: String?) async -> DraftPassage? {
        narrator.discardSession()
        guard generation == token, !resumeWhenActive else { return nil }
        if !isForeground {
            parkForForeground()
            return nil
        }
        guard interruptionAttempts < 1 else {
            fail(BlatherNarrationError.interrupted)
            return nil
        }
        interruptionAttempts += 1
        return await prepareDraft(token: token, pendingSpeech: pendingSpeech)
    }

    private func parkForForeground() {
        resumeWhenActive = true
        generationFailed = true
        errorMessage = nil
    }

    private var isForeground: Bool {
        guard Bundle.main.bundlePath.hasSuffix(".app") else { return true }
        return UIApplication.shared.applicationState == .active
    }

    private func continueAfterInterruption() async {
        guard mode == .live || mode == .replay else { return }
        narrator.discardSession()
        generationFailed = false
        errorMessage = nil
        mode = .live
        let play = wantsAutoplay || isPlaying
        wantsAutoplay = play
        if play, hasAudio {
            isPlaying = true
            hasStartedPlayback = true
            syncPlayback()
        }
        generation &+= 1
        let token = generation
        fillRunning = true
        await runFill(token: token, after: chain)
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
                errorMessage = BlatherModelFailure.isInterrupted(domain: "", code: 0, description: message)
                    ? "Writing paused. Try again."
                    : message
            case .interrupted:
                errorMessage = "Writing paused. Try again."
            }
            return
        }
        if BlatherModelFailure.isInterrupted(error) {
            errorMessage = "Writing paused. Try again."
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

    private var onExpiration: (@MainActor () -> Void)?

    func begin(onExpiration: (@MainActor () -> Void)? = nil) {
        guard id == .invalid else { return }
        self.onExpiration = onExpiration
        // Unit tests run in the test bundle, which has no UIApplication.
        // Hosted in the app, this keeps a model call alive if the phone locks.
        guard Bundle.main.bundlePath.hasSuffix(".app") else { return }
        id = UIApplication.shared.beginBackgroundTask(withName: "Blather") { [weak self] in
            Task { @MainActor in
                self?.expire()
            }
        }
    }

    private func expire() {
        let notify = onExpiration
        onExpiration = nil
        end()
        notify?()
    }

    func end() {
        let current = id
        id = .invalid
        guard current != .invalid else { return }
        UIApplication.shared.endBackgroundTask(current)
    }
}
