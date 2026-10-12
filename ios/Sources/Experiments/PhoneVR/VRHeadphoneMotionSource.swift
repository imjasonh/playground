import CoreMotion
import Foundation
import simd

/// AirPods head tracking for `VRHeadphoneCrossCheck`. Samples arrive on their
/// own operation queue and the cross-check runs once a second on a utility
/// queue, so the render thread never waits on either.
final class VRHeadphoneMotionSource: NSObject, CMHeadphoneMotionManagerDelegate, @unchecked Sendable {
    private let manager = CMHeadphoneMotionManager()
    private let motionQueue = OperationQueue()
    private let checkQueue = DispatchQueue(label: "PhoneVR.airpods", qos: .utility)
    private let phoneMotion: CMMotionManager?
    private var timer: DispatchSourceTimer?
    private let pods = VRLocked(VRRingBuffer<VRRotationSample>(capacity: 500))
    private let phone = VRLocked(VRRingBuffer<VRRotationSample>(capacity: 900))
    private let sensorLocation = VRLocked(0)
    private let connectedBox = VRLocked(false)
    private let yawBias = VRLocked<Float>(0)
    private let latest = VRLocked<VRHeadphoneCrossCheck.Snapshot?>(nil)
    /// Touched only on `checkQueue`.
    private var crossCheck = VRHeadphoneCrossCheck()

    /// With `ownsPhoneMotion`, this reads the phone's gyro itself; otherwise
    /// the caller passes phone samples to `addPhoneSample`.
    init(ownsPhoneMotion: Bool) {
        phoneMotion = ownsPhoneMotion ? CMMotionManager() : nil
        super.init()
        motionQueue.name = "PhoneVR.airpods.motion"
        motionQueue.maxConcurrentOperationCount = 1
    }

    var isAvailable: Bool { manager.isDeviceMotionAvailable }
    var isConnected: Bool { connectedBox.get() }
    var snapshot: VRHeadphoneCrossCheck.Snapshot? { latest.get() }

    static var authorizationStatus: CMAuthorizationStatus { CMHeadphoneMotionManager.authorizationStatus() }

    func start() {
        manager.delegate = self
        manager.startDeviceMotionUpdates(to: motionQueue) { [weak self] motion, _ in
            guard let self, let motion else { return }
            self.pods.withLock { $0.append(Self.sample(motion)) }
            self.sensorLocation.set(motion.sensorLocation.rawValue)
            self.connectedBox.set(true)
        }
        if let phoneMotion, phoneMotion.isDeviceMotionAvailable {
            phoneMotion.deviceMotionUpdateInterval = 1.0 / 100
            phoneMotion.startDeviceMotionUpdates(using: .xArbitraryZVertical, to: motionQueue) { [weak self] motion, _ in
                guard let self, let motion else { return }
                self.phone.withLock { $0.append(Self.sample(motion)) }
            }
        }
        let timer = DispatchSource.makeTimerSource(queue: checkQueue)
        timer.schedule(deadline: .now() + 1, repeating: 1)
        timer.setEventHandler { [weak self] in self?.tick() }
        timer.resume()
        self.timer = timer
    }

    func stop() {
        manager.stopDeviceMotionUpdates()
        manager.delegate = nil
        phoneMotion?.stopDeviceMotionUpdates()
        timer?.cancel()
        timer = nil
    }

    func addPhoneSample(_ sample: VRMotionSample) {
        phone.withLock { $0.append(VRRotationSample(timestamp: sample.timestamp, rate: sample.rotationRate, attitude: sample.attitude)) }
    }

    func setCurrentYawBias(_ bias: Float) {
        yawBias.set(bias)
    }

    private static func sample(_ motion: CMDeviceMotion) -> VRRotationSample {
        let q = motion.attitude.quaternion
        let r = motion.rotationRate
        return VRRotationSample(
            timestamp: motion.timestamp,
            rate: SIMD3(Float(r.x), Float(r.y), Float(r.z)),
            attitude: simd_quatf(ix: Float(q.x), iy: Float(q.y), iz: Float(q.z), r: Float(q.w)).normalized
        )
    }

    private func tick() {
        let phoneSamples = phone.withLock { $0.elements }
        let podSamples = pods.withLock { $0.elements }
        // Core Motion timestamps count seconds since boot, like systemUptime.
        let snapshot = crossCheck.update(
            phone: phoneSamples,
            pods: podSamples,
            podsLocation: sensorLocation.get(),
            now: ProcessInfo.processInfo.systemUptime,
            currentYawBias: yawBias.get()
        )
        latest.set(snapshot)
    }

    func headphoneMotionManagerDidConnect(_ manager: CMHeadphoneMotionManager) {
        connectedBox.set(true)
    }

    func headphoneMotionManagerDidDisconnect(_ manager: CMHeadphoneMotionManager) {
        connectedBox.set(false)
        pods.withLock { $0.removeAll() }
    }
}
