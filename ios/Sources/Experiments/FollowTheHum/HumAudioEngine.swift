import AVFoundation
import Foundation

/// Continuous spatial hum driven by `HumAudioParams`.
///
/// Generates a looping stereo buffer with equal-power pan and a low-pass for
/// muffling when the target is behind you. Works with any headphones; AirPods
/// make left/right steering especially clear.
final class HumAudioEngine {
    private let engine = AVAudioEngine()
    private let player = AVAudioPlayerNode()
    private let eq = AVAudioUnitEQ(numberOfBands: 1)
    private let mixer = AVAudioMixerNode()

    private var phase: Double = 0
    private var currentFrequency: Double = 180
    private var currentPan: Double = 0
    private var isRunning = false
    private var isConnected = false

    init() {
        eq.bands[0].filterType = .lowPass
        eq.bands[0].frequency = 2_400
        eq.bands[0].bandwidth = 1.0
        eq.bands[0].gain = 0
        eq.bands[0].bypass = false

        engine.attach(player)
        engine.attach(eq)
        engine.attach(mixer)

        mixer.outputVolume = 0
    }

    private static var stereoFormat: AVAudioFormat {
        // standardFormatWithSampleRate never fails for 44.1kHz stereo.
        AVAudioFormat(standardFormatWithSampleRate: 44_100, channels: 2)! // pasta:ignore force_unwrap — standard AVAudioFormat
    }

    func start() throws {
        guard !isRunning else { return }
        try connectIfNeeded()
        let session = AVAudioSession.sharedInstance()
        try session.setCategory(.playback, mode: .default, options: [.mixWithOthers])
        try session.setActive(true)

        let buffer = makeHumBuffer(frequency: currentFrequency, pan: currentPan)
        player.scheduleBuffer(buffer, at: nil, options: [.loops], completionHandler: nil)
        do {
            try engine.start()
            try player.playAudio()
        } catch {
            player.stop()
            engine.stop()
            try? session.setActive(false, options: .notifyOthersOnDeactivation)
            throw error
        }
        isRunning = true
    }

    func stop() {
        guard isRunning else { return }
        player.stop()
        engine.stop()
        mixer.outputVolume = 0
        isRunning = false
        try? AVAudioSession.sharedInstance().setActive(false, options: .notifyOthersOnDeactivation)
    }

    /// Smoothly chase the latest game-derived audio parameters.
    func apply(_ params: HumAudioParams) throws {
        let pan = max(-1, min(1, params.pan))
        let volume = Float(max(0, min(1, params.volume)))
        let muffling = max(0, min(1, params.muffling))
        let frequency = params.frequencyHz

        mixer.outputVolume = volume
        // Facing away → darker (lower cutoff); facing target → open and clear.
        eq.bands[0].frequency = Float(900 + (1 - muffling) * 3_600)

        let needsRebuild =
            abs(frequency - currentFrequency) > 4
            || abs(pan - currentPan) > 0.08

        guard isRunning, needsRebuild else { return }

        currentFrequency = frequency
        currentPan = pan
        let buffer = makeHumBuffer(frequency: frequency, pan: pan)
        player.stop()
        player.scheduleBuffer(buffer, at: nil, options: [.loops], completionHandler: nil)
        try player.playAudio()
    }

    private func connectIfNeeded() throws {
        guard !isConnected else { return }
        let format = Self.stereoFormat
        try engine.connectNode(player, to: eq, format: format)
        try engine.connectNode(eq, to: mixer, format: format)
        try engine.connectNode(mixer, to: engine.mainMixerNode, format: format)
        isConnected = true
    }

    private func makeHumBuffer(frequency: Double, pan: Double) -> AVAudioPCMBuffer {
        let format = Self.stereoFormat
        let frames: AVAudioFrameCount = 44_100
        // frameCapacity > 0 with a valid PCM format always succeeds.
        let buffer = AVAudioPCMBuffer(pcmFormat: format, frameCapacity: frames)! // pasta:ignore force_unwrap — AVAudioPCMBuffer
        buffer.frameLength = frames

        guard let left = buffer.floatChannelData?[0],
              let right = buffer.floatChannelData?[1] else { return buffer }

        // Equal-power pan: -1 left … +1 right.
        let angle = (pan + 1) * (.pi / 4) // 0…π/2
        let gainL = Float(cos(angle))
        let gainR = Float(sin(angle))

        let sampleRate = format.sampleRate
        let localPhase = phase

        for i in 0..<Int(frames) {
            let t = Double(i) / sampleRate
            let fundamental = sin(2 * .pi * frequency * t + localPhase)
            let harmonic = 0.22 * sin(2 * .pi * frequency * 2 * t + localPhase)
            let edge = min(Double(i), Double(Int(frames) - 1 - i), 64) / 64
            let window = edge < 1 ? edge : 1
            let sample = Float((fundamental + harmonic) * 0.35 * window)
            left[i] = sample * gainL
            right[i] = sample * gainR
        }

        phase = (localPhase + 2 * .pi * frequency * Double(frames) / sampleRate)
            .truncatingRemainder(dividingBy: 2 * .pi)

        return buffer
    }

    deinit {
        stop()
    }
}
