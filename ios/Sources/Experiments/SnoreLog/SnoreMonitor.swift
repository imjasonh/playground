import AVFoundation
import Foundation
#if canImport(UIKit)
import UIKit
#endif

/// Overnight snore logger: keeps a short rolling mic buffer in RAM, detects
/// sustained loudness spikes, and writes only those clips to disk.
///
/// Requires microphone permission and the `audio` UIBackgroundModes entry so
/// monitoring continues with the screen locked. No App ID entitlements.
@MainActor
final class SnoreMonitor: ObservableObject {
    @Published private(set) var isRunning = false
    @Published private(set) var currentRMS: Double = 0
    @Published private(set) var noiseFloor: Double = 0
    @Published private(set) var threshold: Double = 0
    @Published private(set) var snoreCount = 0
    @Published private(set) var elapsed: TimeInterval = 0
    @Published private(set) var events: [SnoreEvent] = []
    @Published private(set) var statusMessage = "Ready"
    @Published private(set) var lastSavedSession: SleepSession?
    @Published private(set) var currentSessionID: UUID?
    @Published private(set) var microphoneDenied = false

    /// Seconds of audio kept in the ring buffer (pre-roll + event body).
    static let bufferSeconds: Double = 8
    static let sampleRate: Double = 16_000
    /// Extra samples kept after detection ends (within the ring buffer window).
    static let preRollSeconds: Double = 1.0

    let store: SnoreStore
    private let engine = AVAudioEngine()
    private var detector = SnoreDetector()
    private var ring = SnoreRingBuffer(capacity: Int(bufferSeconds * sampleRate))
    private var session: SleepSession?
    private var startUptime: TimeInterval = 0
    private var startDate = Date()
    private var timer: Timer?
    private var pendingPostRoll: PendingClip?
    private var rmsWindow: [Float] = []
    private let rmsWindowSamples = Int(0.1 * sampleRate) // 100 ms

    private struct PendingClip {
        let detection: SnoreDetection
        let captureUntil: TimeInterval
    }

    init(store: SnoreStore = SnoreStore()) {
        self.store = store
    }

    private var now: TimeInterval { ProcessInfo.processInfo.systemUptime - startUptime }

    func start() {
        guard !isRunning else { return }
        microphoneDenied = false

        Task {
            let granted = await requestMicrophone()
            guard granted else {
                microphoneDenied = true
                statusMessage = "Microphone access is required. Enable it in Settings."
                return
            }
            do {
                try beginSession()
            } catch {
                statusMessage = "Couldn't start audio: \(error.localizedDescription)"
                teardownAudio()
            }
        }
    }

    func stop() {
        guard isRunning else { return }
        if let detection = detector.flush(at: now) {
            finalizeClip(for: detection, captureThrough: now)
        } else if let pending = pendingPostRoll {
            finalizeClip(for: pending.detection, captureThrough: now)
            pendingPostRoll = nil
        }

        var finished = session
        finished?.endedAt = Date()
        finished?.durationSeconds = now
        finished?.events = events
        finished?.snoreCount = events.count
        if let finished {
            try? store.save(finished)
            lastSavedSession = finished
        }

        teardownAudio()
        timer?.invalidate()
        timer = nil
        isRunning = false
        #if canImport(UIKit)
        UIApplication.shared.isIdleTimerDisabled = false
        #endif
        statusMessage = events.isEmpty
            ? "Session saved — no snores detected."
            : "Session saved — \(events.count) snore clip\(events.count == 1 ? "" : "s")."
        session = nil
        currentSessionID = nil
    }

    private func beginSession() throws {
        detector.reset()
        ring.reset()
        events = []
        snoreCount = 0
        currentRMS = 0
        elapsed = 0
        pendingPostRoll = nil
        rmsWindow = []
        lastSavedSession = nil

        let newSession = SleepSession(startedAt: Date())
        try store.prepareSession(newSession)
        session = newSession
        currentSessionID = newSession.id
        startDate = newSession.startedAt
        startUptime = ProcessInfo.processInfo.systemUptime

        try configureSession()
        try installTap()
        try engine.start()

        isRunning = true
        statusMessage = "Listening — only loud clips are saved."
        #if canImport(UIKit)
        UIApplication.shared.isIdleTimerDisabled = true
        #endif

        timer = Timer.scheduledTimer(withTimeInterval: 0.5, repeats: true) { [weak self] _ in
            Task { @MainActor in
                self?.elapsed = self?.now ?? 0
                self?.noiseFloor = self?.detector.noiseFloor ?? 0
                self?.threshold = self?.detector.currentThreshold ?? 0
            }
        }
    }

    private func requestMicrophone() async -> Bool {
        await withCheckedContinuation { continuation in
            // AVAudioSession API — available on our iOS 16 deployment target
            // (AVAudioApplication.requestRecordPermission requires iOS 17+).
            AVAudioSession.sharedInstance().requestRecordPermission { granted in
                continuation.resume(returning: granted)
            }
        }
    }

    private func configureSession() throws {
        let session = AVAudioSession.sharedInstance()
        // `.playAndRecord` + `.mixWithOthers` keeps us alive in background audio
        // mode without hijacking other audio too aggressively. Measurement mode
        // disables system AGC so RMS levels stay meaningful.
        try session.setCategory(
            .playAndRecord,
            mode: .measurement,
            options: [.mixWithOthers, .defaultToSpeaker, .allowBluetooth]
        )
        try session.setActive(true)
    }

    private func installTap() throws {
        let input = engine.inputNode
        // Use the hardware format (nil) — converting in the tap format argument
        // is fragile across devices/simulators.
        let hwFormat = input.inputFormat(forBus: 0)
        guard hwFormat.sampleRate > 0, hwFormat.channelCount > 0 else {
            throw MonitorError.noInput
        }

        input.removeTap(onBus: 0)
        let targetRate = Self.sampleRate
        let sourceRate = hwFormat.sampleRate

        input.installTap(onBus: 0, bufferSize: 2048, format: nil) { [weak self] buffer, _ in
            guard let self else { return }
            self.ingest(buffer: buffer, sourceRate: sourceRate, targetRate: targetRate)
        }
    }

    nonisolated private func ingest(buffer: AVAudioPCMBuffer, sourceRate: Double, targetRate: Double) {
        let frameCount = Int(buffer.frameLength)
        guard frameCount > 0, let channels = buffer.floatChannelData else { return }

        // Mix down to mono if the hardware tap is multi-channel.
        let channelCount = Int(buffer.format.channelCount)
        var mono = [Float](repeating: 0, count: frameCount)
        if channelCount <= 1 {
            mono.withUnsafeMutableBufferPointer { dst in
                dst.baseAddress!.update(from: channels[0], count: frameCount)
            }
        } else {
            let scale = 1 / Float(channelCount)
            for c in 0..<channelCount {
                let src = channels[c]
                for i in 0..<frameCount {
                    mono[i] += src[i] * scale
                }
            }
        }

        // Downsample to targetRate with nearest-neighbor (good enough for snore RMS).
        let step = sourceRate / targetRate
        var converted: [Float] = []
        converted.reserveCapacity(max(1, Int(Double(frameCount) / max(step, 1))))
        var cursor = 0.0
        while cursor < Double(frameCount) {
            converted.append(mono[Int(cursor)])
            cursor += step
        }

        Task { @MainActor in
            self.handleSamples(converted)
        }
    }

    private func handleSamples(_ samples: [Float]) {
        guard isRunning else { return }
        samples.withUnsafeBufferPointer { ring.append($0) }

        for sample in samples {
            rmsWindow.append(sample)
            if rmsWindow.count >= rmsWindowSamples {
                let rms = Self.rms(of: rmsWindow)
                rmsWindow.removeAll(keepingCapacity: true)
                currentRMS = rms
                noiseFloor = detector.noiseFloor
                threshold = detector.currentThreshold

                if let detection = detector.process(rms: rms, at: now) {
                    // Keep capturing a bit of post-roll still in the live ring,
                    // then write the clip.
                    pendingPostRoll = PendingClip(
                        detection: detection,
                        captureUntil: now + 0.75
                    )
                }
            }
        }

        if let pending = pendingPostRoll, now >= pending.captureUntil {
            finalizeClip(for: pending.detection, captureThrough: pending.captureUntil)
            pendingPostRoll = nil
        }
    }

    private func finalizeClip(for detection: SnoreDetection, captureThrough: TimeInterval) {
        guard let session else { return }

        let preRoll = Self.preRollSeconds
        let clipStart = max(0, detection.startedAt - preRoll)
        let clipEnd = max(clipStart, captureThrough)
        let duration = min(clipEnd - clipStart, Self.bufferSeconds)
        let sampleCount = Int(duration * Self.sampleRate)
        let samples = ring.recentSamples(sampleCount)

        let eventID = UUID()
        let fileName = "clip-\(eventID.uuidString).caf"
        let url = store.clipURL(sessionID: session.id, fileName: fileName)

        do {
            try SnoreClipWriter.write(samples: samples, sampleRate: Self.sampleRate, to: url)
        } catch {
            statusMessage = "Clip write failed: \(error.localizedDescription)"
            return
        }

        let event = SnoreEvent(
            id: eventID,
            startedAt: startDate.addingTimeInterval(detection.startedAt),
            sessionOffset: detection.startedAt,
            durationSeconds: detection.duration,
            peakRMS: detection.peakRMS,
            noiseFloorAtOnset: detection.noiseFloorAtOnset,
            clipFileName: fileName
        )
        events.insert(event, at: 0)
        snoreCount = events.count

        var updated = session
        updated.events = events
        updated.snoreCount = events.count
        updated.durationSeconds = now
        try? store.save(updated)
        self.session = updated
        statusMessage = "Logged snore #\(snoreCount)"
    }

    private func teardownAudio() {
        engine.inputNode.removeTap(onBus: 0)
        if engine.isRunning { engine.stop() }
        try? AVAudioSession.sharedInstance().setActive(false, options: .notifyOthersOnDeactivation)
    }

    private static func rms(of samples: [Float]) -> Double {
        guard !samples.isEmpty else { return 0 }
        var sum: Double = 0
        for s in samples {
            let v = Double(s)
            sum += v * v
        }
        return sqrt(sum / Double(samples.count))
    }

    enum MonitorError: Error {
        case noInput
    }
}
