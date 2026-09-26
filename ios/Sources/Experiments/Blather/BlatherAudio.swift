import AVFoundation
import Foundation
import FoundationModels

/// Reads `SystemLanguageModel` availability into the shared gate.
enum BlatherAvailability {
    static func current() -> AgentModelGate {
        switch SystemLanguageModel.default.availability {
        case .available:
            return .available
        case .unavailable(.deviceNotEligible):
            return .deviceNotEligible
        case .unavailable(.appleIntelligenceNotEnabled):
            return .needsAppleIntelligence
        case .unavailable(.modelNotReady):
            return .modelNotReady
        case .unavailable(let reason):
            return .other("Apple Intelligence isn't available (\(String(describing: reason))).")
        @unknown default:
            return .other("Apple Intelligence isn't available on this device.")
        }
    }
}

/// On-device Foundation Model narrator.
///
/// Each compact starts a new `LanguageModelSession`. The previous session is
/// dropped because its transcript cannot be pruned in place.
@MainActor
final class BlatherOnDeviceNarrator: BlatherNarrator {
    private var session: LanguageModelSession?

    func prepare() {
        guard BlatherAvailability.current().isAvailable else { return }
        if session == nil {
            let created = LanguageModelSession(instructions: BlatherScript.instructions)
            created.prewarm()
            session = created
        } else {
            session?.prewarm()
        }
    }

    func discardSession() {
        session = nil
    }

    func narrate(prompt: String, freshSession: Bool) async throws -> BlatherNarration {
        let gate = BlatherAvailability.current()
        guard gate.isAvailable else {
            throw BlatherNarrationError.modelUnavailable(gate.detail)
        }
        if freshSession || session == nil {
            let created = LanguageModelSession(instructions: BlatherScript.instructions)
            created.prewarm()
            session = created
        }
        guard let session else {
            throw BlatherNarrationError.failed("The model session is missing.")
        }
        do {
            let response = try await session.respond(to: prompt)
            let text = response.content.trimmingCharacters(in: .whitespacesAndNewlines)
            return BlatherNarration(text: text, totalTokenCount: response.usage.totalTokenCount)
        } catch {
            self.session = nil
            if OnDeviceContextManager.isExceededContextWindow(error) {
                throw BlatherNarrationError.contextExceeded
            }
            if error is CancellationError {
                throw error
            }
            if BlatherModelFailure.isInterrupted(error) {
                throw BlatherNarrationError.interrupted
            }
            throw BlatherNarrationError.failed(error.localizedDescription)
        }
    }

    /// Prefers a US English premium voice, then any enhanced English voice.
    static func preferredVoice() -> AVSpeechSynthesisVoice? {
        let voices = AVSpeechSynthesisVoice.speechVoices()
        let english = voices.filter { $0.language.hasPrefix("en") }
        let pool = english.isEmpty ? voices : english
        return pool.max { lhs, rhs in
            rank(lhs) < rank(rhs)
        }
    }

    private static func rank(_ voice: AVSpeechSynthesisVoice) -> Int {
        let quality: Int
        switch voice.quality {
        case .premium:
            quality = 3
        case .enhanced:
            quality = 2
        case .default:
            quality = 1
        @unknown default:
            quality = 1
        }
        let unitedStates = voice.language == "en-US" ? 1 : 0
        return quality * 2 + unitedStates
    }
}

enum BlatherSpeechError: Error {
    case emptyAudio
    case unreadableBuffer
}

/// Writes `AVSpeechSynthesizer` buffers to a CAF file and does not play them.
@MainActor
final class BlatherSpeechRenderer: BlatherSynthesizer {
    private let synthesizer = AVSpeechSynthesizer()

    func synthesize(_ text: String, to fileURL: URL) async throws -> TimeInterval {
        let utterance = AVSpeechUtterance(string: text)
        utterance.voice = BlatherOnDeviceNarrator.preferredVoice()
        utterance.rate = AVSpeechUtteranceDefaultSpeechRate
        return try await withCheckedThrowingContinuation { (continuation: CheckedContinuation<TimeInterval, Error>) in
            let box = OnceResume(continuation)
            let writer = SpeechFileWriter(url: fileURL)
            synthesizer.write(utterance) { buffer in
                switch writer.take(buffer) {
                case .keepGoing:
                    break
                case .finished(let duration):
                    box.resume(returning: duration)
                case .failed(let error):
                    box.resume(throwing: error)
                }
            }
        }
    }
}

/// Plays episode files in order and reports a single timeline playhead.
///
/// Speeds stay inside `AVAudioPlayer.rate` (0.5× through 2×). The player
/// keeps the voice at the same pitch.
@MainActor
final class BlatherAVPlayback: NSObject, BlatherPlaybackControlling, AVAudioPlayerDelegate {
    var onPlayhead: ((TimeInterval) -> Void)?
    var onEnded: (() -> Void)?
    var onInterruption: ((Bool, Bool) -> Void)?
    var onRouteLost: (() -> Void)?

    private var segments: [BlatherPlayable] = []
    private var index = 0
    private var player: AVAudioPlayer?
    private var playing = false
    private var rate: Float = 1
    private var timer: Timer?
    private var reportedPlayhead: TimeInterval = 0
    private var didSignalEnd = false
    private var observers: [NSObjectProtocol] = []

    override init() {
        super.init()
        let center = NotificationCenter.default
        let session = AVAudioSession.sharedInstance()
        observers.append(center.addObserver(
            forName: AVAudioSession.didBecomeInactiveNotification,
            object: session,
            queue: .main
        ) { [weak self] note in
            Task { @MainActor in
                self?.handleInactive(note)
            }
        })
        observers.append(center.addObserver(
            forName: AVAudioSession.resumptionRecommendationNotification,
            object: session,
            queue: .main
        ) { [weak self] note in
            Task { @MainActor in
                self?.handleResumption(note)
            }
        })
        observers.append(center.addObserver(
            forName: AVAudioSession.routeChangeNotification,
            object: session,
            queue: .main
        ) { [weak self] note in
            Task { @MainActor in
                self?.handleRouteChange(note)
            }
        })
    }

    func update(segments: [BlatherPlayable], playhead: TimeInterval, playing: Bool, rate: Double) {
        let grew = segments.count > self.segments.count
        let rewound = playhead + 0.2 < reportedPlayhead
        if grew || rewound {
            didSignalEnd = false
        }
        self.segments = segments
        self.rate = Float(rate)
        if segments.isEmpty {
            player?.stop()
            player = nil
            self.playing = false
            stopTimer()
            reportedPlayhead = 0
            index = 0
            return
        }
        let location = BlatherTimeline.locate(playhead, durations: segments.map(\.duration))
        let drift = abs(playhead - reportedPlayhead)
        if player == nil || drift > 0.35 || location.index != index {
            load(index: location.index, offset: location.offset)
        }
        applyRate()
        let finished = isFinished(playhead)
        self.playing = playing && !finished
        if self.playing {
            activateSession()
            self.player?.play()
            startTimer()
        } else {
            self.player?.pause()
            stopTimer()
        }
        reportedPlayhead = playhead
    }

    func stop() {
        playing = false
        timer?.invalidate()
        timer = nil
        player?.stop()
        player = nil
        segments = []
        index = 0
        reportedPlayhead = 0
        for observer in observers {
            NotificationCenter.default.removeObserver(observer)
        }
        observers = []
    }

    nonisolated func audioPlayerDidFinishPlaying(_ player: AVAudioPlayer, successfully _: Bool) {
        let finished = player
        Task { @MainActor in
            self.advance(from: finished)
        }
    }

    private func tick() {
        guard playing, let player, let segment = currentSegment else { return }
        if player.currentTime >= segment.duration - 0.05 {
            advance(from: player)
            return
        }
        publish(playhead: elapsed(player: player))
    }

    private func advance(from player: AVAudioPlayer) {
        guard player === self.player else { return }
        if index + 1 < segments.count {
            didSignalEnd = false
            load(index: index + 1, offset: 0)
            applyRate()
            if playing {
                self.player?.play()
            }
            if let current = self.player {
                publish(playhead: elapsed(player: current))
            }
            return
        }
        signalEnd()
    }

    private func signalEnd() {
        playing = false
        player?.pause()
        stopTimer()
        let total = segments.reduce(0) { $0 + $1.duration }
        publish(playhead: total)
        guard !didSignalEnd else { return }
        didSignalEnd = true
        onEnded?()
    }

    private func publish(playhead: TimeInterval) {
        reportedPlayhead = playhead
        onPlayhead?(playhead)
    }

    private func elapsed(player: AVAudioPlayer) -> TimeInterval {
        let prior = segments.prefix(index).reduce(0) { $0 + $1.duration }
        let local = min(player.currentTime, currentSegment?.duration ?? player.currentTime)
        return prior + max(0, local)
    }

    private func applyRate() {
        guard let player else { return }
        if !player.enableRate {
            player.enableRate = true
        }
        if player.rate != rate {
            player.rate = rate
        }
    }

    private var currentSegment: BlatherPlayable? {
        guard segments.indices.contains(index) else { return nil }
        return segments[index]
    }

    private func isFinished(_ playhead: TimeInterval) -> Bool {
        let total = segments.reduce(0) { $0 + $1.duration }
        return total > 0 && playhead >= total - 0.05
    }

    private func load(index: Int, offset: TimeInterval) {
        guard segments.indices.contains(index) else { return }
        let segment = segments[index]
        self.index = index
        do {
            let player = try AVAudioPlayer(contentsOf: segment.url)
            player.delegate = self
            player.enableRate = true
            player.prepareToPlay()
            if player.duration > 0 {
                let upper = max(0, player.duration - 0.01)
                player.currentTime = min(max(0, offset), upper)
            }
            player.rate = rate
            self.player = player
        } catch {
            self.player = nil
        }
    }

    private func activateSession() {
        let session = AVAudioSession.sharedInstance()
        try? session.setCategory(.playback, mode: .spokenAudio, options: [])
        try? session.setActive(true)
    }

    private func startTimer() {
        guard timer == nil else { return }
        let timer = Timer(timeInterval: 0.25, repeats: true) { [weak self] _ in
            Task { @MainActor in
                self?.tick()
            }
        }
        RunLoop.main.add(timer, forMode: .common)
        self.timer = timer
    }

    private func stopTimer() {
        timer?.invalidate()
        timer = nil
    }

    private func handleInactive(_ note: Notification) {
        guard let context = note.userInfo?[AVAudioSession.deactivationContextKey] as? AVAudioSession.DeactivationContext,
              context.source == .system else {
            return
        }
        onInterruption?(true, false)
    }

    private func handleResumption(_ note: Notification) {
        let context = note.userInfo?[AVAudioSession.resumptionContextKey] as? AVAudioSession.ResumptionContext
        onInterruption?(false, context?.recommendation == .shouldResume)
    }

    private func handleRouteChange(_ note: Notification) {
        guard let raw = note.userInfo?[AVAudioSessionRouteChangeReasonKey] as? UInt,
              let reason = AVAudioSession.RouteChangeReason(rawValue: raw),
              reason == .oldDeviceUnavailable else {
            return
        }
        onRouteLost?()
    }
}

/// Resumes a continuation once. Speech callbacks can arrive off the main thread.
private final class OnceResume<T>: @unchecked Sendable {
    private let lock = NSLock()
    private var resumed = false
    private var result: Result<T, Error>?
    private let continuation: CheckedContinuation<T, Error>

    init(_ continuation: CheckedContinuation<T, Error>) {
        self.continuation = continuation
    }

    func resume(returning value: T) {
        schedule(.success(value))
    }

    func resume(throwing error: Error) {
        schedule(.failure(error))
    }

    /// Hops to the main queue so a speech callback cannot re-enter `write`.
    private func schedule(_ result: Result<T, Error>) {
        lock.lock()
        if resumed {
            lock.unlock()
            return
        }
        resumed = true
        self.result = result
        lock.unlock()
        DispatchQueue.main.async { [self] in
            self.lock.lock()
            let pending = self.result
            self.result = nil
            self.lock.unlock()
            guard let pending else { return }
            switch pending {
            case .success(let value):
                self.continuation.resume(returning: value)
            case .failure(let error):
                self.continuation.resume(throwing: error)
            }
        }
    }
}

/// Collects synthesizer buffers into a 16-bit CAF the player can open.
private final class SpeechFileWriter: @unchecked Sendable {
    enum Action {
        case keepGoing
        case finished(TimeInterval)
        case failed(Error)
    }

    private let url: URL
    private var file: AVAudioFile?
    private var converter: AVAudioConverter?
    private var targetFormat: AVAudioFormat?
    private var frames: AVAudioFramePosition = 0
    private var sampleRate: Double = 0
    private var closed = false

    init(url: URL) {
        self.url = url
    }

    func take(_ buffer: AVAudioBuffer) -> Action {
        if closed { return .keepGoing }
        guard let pcm = buffer as? AVAudioPCMBuffer else {
            closed = true
            finishFile()
            return .failed(BlatherSpeechError.unreadableBuffer)
        }
        if pcm.frameLength == 0 {
            closed = true
            finishFile()
            guard frames > 0, sampleRate > 0 else {
                try? FileManager.default.removeItem(at: url)
                return .failed(BlatherSpeechError.emptyAudio)
            }
            return .finished(Double(frames) / sampleRate)
        }
        do {
            try append(pcm)
            return .keepGoing
        } catch {
            closed = true
            finishFile()
            try? FileManager.default.removeItem(at: url)
            return .failed(error)
        }
    }

    private func append(_ pcm: AVAudioPCMBuffer) throws {
        if file == nil {
            guard pcm.format.sampleRate > 0 else { throw BlatherSpeechError.unreadableBuffer }
            let channels = max(1, pcm.format.channelCount)
            guard let target = AVAudioFormat(
                commonFormat: .pcmFormatInt16,
                sampleRate: pcm.format.sampleRate,
                channels: channels,
                interleaved: true
            ) else {
                throw BlatherSpeechError.unreadableBuffer
            }
            guard let converter = AVAudioConverter(from: pcm.format, to: target) else {
                throw BlatherSpeechError.unreadableBuffer
            }
            try FileManager.default.createDirectory(
                at: url.deletingLastPathComponent(),
                withIntermediateDirectories: true
            )
            if FileManager.default.fileExists(atPath: url.path) {
                try FileManager.default.removeItem(at: url)
            }
            var settings = target.settings
            settings[AVFormatIDKey] = kAudioFormatLinearPCM
            file = try AVAudioFile(
                forWriting: url,
                settings: settings,
                commonFormat: .pcmFormatInt16,
                interleaved: true
            )
            self.converter = converter
            targetFormat = target
            sampleRate = target.sampleRate
        }
        guard let converter, let targetFormat, let file else {
            throw BlatherSpeechError.unreadableBuffer
        }
        let ratio = targetFormat.sampleRate / pcm.format.sampleRate
        let capacity = AVAudioFrameCount((Double(pcm.frameLength) * ratio).rounded(.up)) + 32
        guard let converted = AVAudioPCMBuffer(pcmFormat: targetFormat, frameCapacity: max(capacity, 1)) else {
            throw BlatherSpeechError.unreadableBuffer
        }
        var convertError: NSError?
        let input = BufferBox(pcm)
        let status = converter.convert(to: converted, error: &convertError) { _, outStatus in
            if let buffer = input.take() {
                outStatus.pointee = .haveData
                return buffer
            }
            outStatus.pointee = .noDataNow
            return nil
        }
        if let convertError { throw convertError }
        if status == .error { throw BlatherSpeechError.unreadableBuffer }
        guard converted.frameLength > 0 else { return }
        try file.write(from: converted)
        frames += AVAudioFramePosition(converted.frameLength)
    }

    private func finishFile() {
        file = nil
    }
}

/// Hands one PCM buffer to `AVAudioConverter` and then reports no more data.
private final class BufferBox: @unchecked Sendable {
    private var buffer: AVAudioPCMBuffer?

    init(_ buffer: AVAudioPCMBuffer) {
        self.buffer = buffer
    }

    func take() -> AVAudioPCMBuffer? {
        let current = buffer
        buffer = nil
        return current
    }
}
