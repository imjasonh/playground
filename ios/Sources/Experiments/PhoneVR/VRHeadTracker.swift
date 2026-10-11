import Foundation
import simd

/// One Core Motion device-motion sample.
struct VRMotionSample {
    /// Seconds on the host clock (`CMLogItem.timestamp`).
    var timestamp: TimeInterval
    /// `CMAttitude.quaternion`: maps device-frame vectors into Core Motion's reference frame.
    var attitude: simd_quatf
    /// Bias-corrected angular velocity in the device frame, radians per second.
    var rotationRate: SIMD3<Float>
}

/// One ARKit camera pose.
struct VRTrackingSample {
    enum Quality: Equatable {
        case normal
        case limited
        case unavailable
    }

    /// Capture time on the host clock (`ARFrame.timestamp`).
    var timestamp: TimeInterval
    /// `ARCamera.transform`.
    var worldFromCamera: simd_float4x4
    var quality: Quality
}

enum VRTrackingMode: String, Equatable {
    /// ARKit position plus Core Motion rotation.
    case sixDoF
    /// Core Motion rotation with a neck model; the position stays put.
    case threeDoF
}

/// Predicted pose of the screen frame (the head) in the ARKit world.
struct VRHeadPose {
    var worldFromScreen: VRPose
    var mode: VRTrackingMode
    /// Time the prediction looked ahead of the newest gyro sample.
    var rotationHorizon: TimeInterval
    /// Time the prediction looked ahead of the newest ARKit pose.
    var translationHorizon: TimeInterval
    var motionTimestamp: TimeInterval?
}

/// Fuses ARKit's camera-rate 6DoF pose with Core Motion's 100 Hz attitude and
/// predicts the head pose for a display time.
///
/// Rotation comes from Core Motion: its attitude is mapped into the ARKit
/// world through a yaw offset that a slow filter estimates from paired ARKit
/// and Core Motion samples, then extrapolated with the newest gyro rate.
/// Translation comes from ARKit, extrapolated with a filtered velocity. When
/// ARKit tracking is limited or off, the position pivots on a neck model.
struct VRHeadTracker {
    struct Configuration {
        var frames: VRDeviceFrames
        var predictionEnabled = true
        var maxRotationHorizon: TimeInterval = 0.05
        var maxTranslationHorizon: TimeInterval = 0.06
        /// Time constant of the Core Motion to ARKit yaw alignment.
        var yawTimeConstant: TimeInterval = 2.0
        /// Faster time constant used while the alignment is far off, such as
        /// after ARKit relocalizes, so the correction lands in about a second.
        var yawCatchUpTimeConstant: TimeInterval = 0.5
        var yawCatchUpThreshold: Float = VRMath.radians(6)
        var velocitySmoothing: Float = 0.35
        /// Screen centre relative to the neck pivot, in the screen frame. The
        /// pivot sits about 8 cm below and 9 cm behind the eyes.
        var neckToScreen = SIMD3<Float>(0, 0.08, -0.156)
        /// Time constant for gliding out a position step instead of popping.
        var positionBlendTimeConstant: TimeInterval = 0.25
        /// A single-frame ARKit position change larger than this is a relocalization, not motion.
        var positionJumpThreshold: Float = 0.2

        init(frames: VRDeviceFrames) {
            self.frames = frames
        }
    }

    private(set) var configuration: Configuration
    private var motion = VRRingBuffer<VRMotionSample>(capacity: 128)

    /// Yaw of Core Motion's reference frame in the ARKit world, radians.
    private(set) var yawOffset: Float = 0
    private(set) var hasYawOffset = false
    /// Extra yaw added to the alignment, such as the AirPods drift cross-check.
    var yawBias: Float = 0
    private var lastYawUpdate: TimeInterval?

    private(set) var mode: VRTrackingMode = .threeDoF
    /// False until ARKit reports its first normal pose. Before that the 3DoF
    /// position is arbitrary, so the first fix snaps instead of gliding.
    private var hasTracked = false
    private var lastTrackedTime: TimeInterval?
    private var lastTrackedPosition: SIMD3<Float>?
    private var lastTrackedRotation: simd_quatf?
    private(set) var velocity: SIMD3<Float> = .zero
    private var neckPivot: SIMD3<Float> = .zero
    private var blendOffset: SIMD3<Float> = .zero
    private var blendStart: TimeInterval = 0

    init(configuration: Configuration) {
        self.configuration = configuration
    }

    var latestMotion: VRMotionSample? { motion.last }

    mutating func setPredictionEnabled(_ enabled: Bool) {
        configuration.predictionEnabled = enabled
    }

    mutating func ingest(_ sample: VRMotionSample) {
        if let last = motion.last {
            if sample.timestamp <= last.timestamp {
                if last.timestamp - sample.timestamp > 1 { motion.removeAll() } else { return }
            }
        }
        motion.append(sample)
    }

    mutating func ingest(_ sample: VRTrackingSample) {
        guard sample.quality == .normal else {
            enterThreeDoF(at: sample.timestamp)
            return
        }
        let worldFromCamera = VRPose(sample.worldFromCamera)
        let worldFromScreen = worldFromCamera * configuration.frames.cameraFromScreen
        updateYawOffset(worldFromCamera: worldFromCamera.rotation, at: sample.timestamp)

        let position = worldFromScreen.position
        if mode == .threeDoF {
            let before = predictHead(at: sample.timestamp).worldFromScreen.position
            mode = .sixDoF
            velocity = .zero
            if hasTracked {
                startBlend(from: before, to: position, at: sample.timestamp)
            } else {
                blendOffset = .zero
                hasTracked = true
            }
        } else if let lastTime = lastTrackedTime, let lastPosition = lastTrackedPosition {
            let dt = sample.timestamp - lastTime
            let step = position - lastPosition
            if dt > 0, dt < 0.25 {
                if simd_length(step) > configuration.positionJumpThreshold {
                    let before = currentBlendedPosition(at: sample.timestamp, base: lastPosition + velocity * Float(dt))
                    velocity = .zero
                    startBlend(from: before, to: position, at: sample.timestamp)
                } else {
                    let measured = step / Float(dt)
                    velocity += (measured - velocity) * configuration.velocitySmoothing
                }
            } else {
                velocity = .zero
            }
        }
        lastTrackedTime = sample.timestamp
        lastTrackedPosition = position
        lastTrackedRotation = worldFromScreen.rotation
    }

    /// Rotation of the screen frame in the world at `time`.
    func predictRotation(at time: TimeInterval) -> simd_quatf {
        predictRotationAndHorizon(at: time).rotation
    }

    func predictHead(at time: TimeInterval) -> VRHeadPose {
        let (rotation, rotationHorizon) = predictRotationAndHorizon(at: time)
        var translationHorizon: TimeInterval = 0
        let position: SIMD3<Float>
        switch mode {
        case .sixDoF:
            var base = lastTrackedPosition ?? .zero
            if let trackedTime = lastTrackedTime, configuration.predictionEnabled {
                translationHorizon = min(max(time - trackedTime, 0), configuration.maxTranslationHorizon)
                base += velocity * Float(translationHorizon)
            }
            position = currentBlendedPosition(at: time, base: base)
        case .threeDoF:
            position = currentBlendedPosition(at: time, base: neckPivot + rotation.act(configuration.neckToScreen))
        }
        return VRHeadPose(
            worldFromScreen: VRPose(rotation: rotation, position: position),
            mode: mode,
            rotationHorizon: rotationHorizon,
            translationHorizon: translationHorizon,
            motionTimestamp: motion.last?.timestamp
        )
    }

    /// Core Motion attitude at `time`, interpolated between samples.
    func attitude(at time: TimeInterval) -> simd_quatf? {
        guard let newest = motion.last, let oldest = motion.first else { return nil }
        if time >= newest.timestamp {
            let ahead = time - newest.timestamp
            guard ahead <= 0.03 else { return nil }
            return VRMath.integrate(newest.attitude, bodyRate: newest.rotationRate, dt: Float(ahead))
        }
        guard time >= oldest.timestamp else { return nil }
        var hi = motion.count - 1
        var lo = 0
        while hi - lo > 1 {
            let mid = (lo + hi) / 2
            if motion[mid].timestamp <= time { lo = mid } else { hi = mid }
        }
        let a = motion[lo]
        let b = motion[hi]
        let span = b.timestamp - a.timestamp
        let f = span > 0 ? Float((time - a.timestamp) / span) : 0
        return simd_slerp(a.attitude, b.attitude, f)
    }

    // MARK: - Private

    private func predictRotationAndHorizon(at time: TimeInterval) -> (rotation: simd_quatf, horizon: TimeInterval) {
        let frames = configuration.frames
        guard let newest = motion.last else {
            return (lastTrackedRotation ?? VRMath.identityRotation, 0)
        }
        var horizon: TimeInterval = 0
        if configuration.predictionEnabled {
            horizon = min(max(time - newest.timestamp, 0), configuration.maxRotationHorizon)
        }
        let attitude = VRMath.integrate(newest.attitude, bodyRate: newest.rotationRate, dt: Float(horizon))
        let worldFromReference = VRDeviceFrames.worldFromReference(yaw: yawOffset + yawBias)
        let worldFromCamera = worldFromReference * attitude * VRDeviceFrames.deviceFromCamera
        return ((worldFromCamera * frames.cameraFromScreen.rotation).normalized, horizon)
    }

    private mutating func updateYawOffset(worldFromCamera: simd_quatf, at time: TimeInterval) {
        guard let attitude = attitude(at: time) else { return }
        let worldFromReference = worldFromCamera * VRDeviceFrames.deviceFromCamera.inverse * attitude.inverse
        let measured = VRMath.yawAboutUp(of: worldFromReference * VRDeviceFrames.worldFromReferenceBase.inverse)
        guard hasYawOffset, let last = lastYawUpdate else {
            yawOffset = measured
            hasYawOffset = true
            lastYawUpdate = time
            return
        }
        let dt = min(max(time - last, 0), 0.1)
        lastYawUpdate = time
        let error = VRMath.wrapAngle(measured - yawOffset)
        let tau = abs(error) > configuration.yawCatchUpThreshold
            ? configuration.yawCatchUpTimeConstant
            : configuration.yawTimeConstant
        // Paired samples disagree most while the head turns fast, because the
        // ARKit and gyro timestamps are not perfectly aligned. Trust them less then.
        let speed = simd_length(motion.last?.rotationRate ?? .zero)
        let weight = 1 / (1 + (speed / 2) * (speed / 2))
        yawOffset = VRMath.wrapAngle(yawOffset + error * VRMath.blendFactor(dt: dt, tau: tau) * weight)
    }

    private mutating func enterThreeDoF(at time: TimeInterval) {
        guard mode == .sixDoF else { return }
        let pose = predictHead(at: time).worldFromScreen
        mode = .threeDoF
        velocity = .zero
        neckPivot = pose.position - pose.rotation.act(configuration.neckToScreen)
        blendOffset = .zero
        lastTrackedTime = nil
        lastTrackedPosition = nil
    }

    private mutating func startBlend(from before: SIMD3<Float>, to after: SIMD3<Float>, at time: TimeInterval) {
        blendOffset = before - after
        blendStart = time
    }

    private func currentBlendedPosition(at time: TimeInterval, base: SIMD3<Float>) -> SIMD3<Float> {
        let elapsed = max(0, time - blendStart)
        let remaining = Float(exp(-elapsed / configuration.positionBlendTimeConstant))
        return base + blendOffset * remaining
    }
}
