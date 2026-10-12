import AVFoundation
import simd

/// World-locked spatial audio. A humming beacon orbits the play area and the
/// listener follows the fused VR head pose, so the sound stays put in the
/// scene as you turn. System head tracking stays off: the phone is strapped
/// to the head, so the system's phone-relative tracking would add nothing or
/// apply the rotation twice.
final class VRAudio: @unchecked Sendable {
    /// Oscillator state, touched only on the audio render thread.
    private final class Hum: @unchecked Sendable {
        private let sampleRate: Double
        private var phase: Double = 0
        private var tremoloPhase: Double = 0

        init(sampleRate: Double) {
            self.sampleRate = sampleRate
        }

        func next() -> Float {
            let twoPi = 2 * Double.pi
            phase += twoPi * 196 / sampleRate
            if phase > twoPi { phase -= twoPi }
            tremoloPhase += twoPi * 0.35 / sampleRate
            if tremoloPhase > twoPi { tremoloPhase -= twoPi }
            let tone = sin(phase) + 0.35 * sin(2 * phase) + 0.12 * sin(3 * phase)
            return Float(tone * (0.75 + 0.25 * sin(tremoloPhase)) * 0.18)
        }
    }

    private let engine = AVAudioEngine()
    private let environment = AVAudioEnvironmentNode()
    /// Audio session and engine calls can block, so they run here instead of
    /// on the main thread.
    private let queue = DispatchQueue(label: "PhoneVR.audio", qos: .userInitiated)
    /// The beacon while the engine runs. The render thread reads it.
    private let beacon = VRLocked<AVAudioSourceNode?>(nil)
    /// Touched only on `queue`.
    private var observer: NSObjectProtocol?

    func start() {
        queue.async { try? self.startEngine() }
    }

    func stop() {
        queue.async { self.stopEngine() }
    }

    private func startEngine() throws {
        let session = AVAudioSession.sharedInstance()
        try session.setCategory(.playback, mode: .default, options: [])
        try session.setActive(true)
        let hardwareRate = engine.outputNode.outputFormat(forBus: 0).sampleRate
        let sampleRate = hardwareRate > 0 ? hardwareRate : 48_000
        guard let mono = AVAudioFormat(standardFormatWithSampleRate: sampleRate, channels: 1),
              let stereo = AVAudioFormat(standardFormatWithSampleRate: sampleRate, channels: 2) else { return }
        let hum = Hum(sampleRate: sampleRate)
        let node = AVAudioSourceNode(format: mono) { _, _, frameCount, bufferList -> OSStatus in
            let buffers = UnsafeMutableAudioBufferListPointer(bufferList)
            for frame in 0..<Int(frameCount) {
                let value = hum.next()
                for buffer in buffers {
                    guard let data = buffer.mData?.assumingMemoryBound(to: Float.self) else { continue }
                    data[frame] = value
                }
            }
            return noErr
        }
        engine.attach(environment)
        engine.attach(node)
        try engine.connectNode(node, to: environment, format: mono)
        try engine.connectNode(environment, to: engine.mainMixerNode, format: stereo)
        node.renderingAlgorithm = .HRTFHQ
        node.reverbBlend = 0.25
        environment.reverbParameters.enable = true
        environment.reverbParameters.loadFactoryReverbPreset(.mediumRoom)
        environment.reverbParameters.level = -10
        environment.distanceAttenuationParameters.distanceAttenuationModel = .inverse
        environment.distanceAttenuationParameters.referenceDistance = 1
        environment.distanceAttenuationParameters.maximumDistance = 30
        engine.prepare()
        try engine.start()
        beacon.set(node)
        observer = NotificationCenter.default.addObserver(forName: .AVAudioEngineConfigurationChange, object: engine, queue: nil) { [weak self] _ in
            self?.queue.async { self?.restartAfterConfigurationChange() }
        }
    }

    private func restartAfterConfigurationChange() {
        guard beacon.get() != nil, !engine.isRunning else { return }
        try? engine.start()
    }

    private func stopEngine() {
        beacon.set(nil)
        if let observer { NotificationCenter.default.removeObserver(observer) }
        observer = nil
        engine.stop()
        try? AVAudioSession.sharedInstance().setActive(false, options: .notifyOthersOnDeactivation)
    }

    /// Places the listener and the beacon, both in scene coordinates. Called
    /// from the render thread once per frame.
    func update(listener: VRPose, beaconPosition: SIMD3<Float>) {
        guard let beacon = beacon.get() else { return }
        let p = listener.position
        let forward = listener.rotation.act(SIMD3(0, 0, -1))
        let up = listener.rotation.act(SIMD3(0, 1, 0))
        environment.listenerPosition = AVAudio3DPoint(x: p.x, y: p.y, z: p.z)
        environment.listenerVectorOrientation = AVAudio3DVectorOrientation(
            forward: AVAudio3DVector(x: forward.x, y: forward.y, z: forward.z),
            up: AVAudio3DVector(x: up.x, y: up.y, z: up.z)
        )
        beacon.position = AVAudio3DPoint(x: beaconPosition.x, y: beaconPosition.y, z: beaconPosition.z)
    }
}
