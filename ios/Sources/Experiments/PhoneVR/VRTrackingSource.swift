import ARKit
import AVFoundation
import CoreMotion
import simd

/// The newest ARKit camera image, kept only while passthrough wants it.
struct VRCameraFrame {
    var pixelBuffer: CVPixelBuffer
    var timestamp: TimeInterval
    var worldFromCamera: simd_float4x4
    /// Pixel intrinsics: fx, fy at [0][0], [1][1]; cx, cy at [2][0], [2][1].
    var intrinsics: simd_float3x3
    var imageWidth: Float
    var imageHeight: Float
}

/// Runs ARKit world tracking and Core Motion for the render thread.
///
/// ARKit calls back on its own serial queue; this copies what the render
/// thread needs into locked mailboxes so the render thread never waits on
/// ARKit. Core Motion is polled, not queued, so the render thread always
/// reads the newest sample.
final class VRTrackingSource: NSObject, ARSessionDelegate, @unchecked Sendable {
    enum CameraState: Equatable {
        case off
        case starting
        case running
        case failed(String)
    }

    private struct Mailbox {
        var tracking: VRTrackingSample?
        var floorHeight: Float?
        var camera: VRCameraFrame?
        var voxelCapture: VRVoxelCaptureFrame?
        var wantsCamera = false
        var wantsVoxelCapture = false
        var state: CameraState = .off
        var formatDescription: String?
    }

    let session = ARSession()
    private let motionManager = CMMotionManager()
    private let delegateQueue = DispatchQueue(label: "PhoneVR.arkit", qos: .userInteractive)
    private let mailbox = VRLocked(Mailbox())
    private var configuration: ARWorldTrackingConfiguration?
    private var lookingForFloor = false

    static var supportsWorldTracking: Bool { ARWorldTrackingConfiguration.isSupported }

    var isMotionAvailable: Bool { motionManager.isDeviceMotionAvailable }

    var cameraState: CameraState { mailbox.withLock { $0.state } }

    var videoFormatDescription: String? { mailbox.withLock { $0.formatDescription } }

    /// Starts Core Motion and, when `worldTracking` is true, ARKit.
    func start(worldTracking: Bool) {
        if motionManager.isDeviceMotionAvailable {
            motionManager.deviceMotionUpdateInterval = 1.0 / 200
            // No magnetometer: its corrections would show up as sudden yaw jumps.
            motionManager.startDeviceMotionUpdates(using: .xArbitraryZVertical)
        }
        guard worldTracking, Self.supportsWorldTracking else { return }
        let configuration = ARWorldTrackingConfiguration()
        configuration.worldAlignment = .gravity
        configuration.planeDetection = [.horizontal]
        configuration.isLightEstimationEnabled = false
        configuration.environmentTexturing = .none
        if let format = Self.preferredVideoFormat() {
            configuration.videoFormat = format
            let size = format.imageResolution
            mailbox.withLock { $0.formatDescription = "\(Int(size.width))×\(Int(size.height)) at \(format.framesPerSecond) fps" }
        }
        self.configuration = configuration
        lookingForFloor = true
        session.delegate = self
        session.delegateQueue = delegateQueue
        mailbox.withLock { $0.state = .starting }
        session.run(configuration, options: [.resetTracking, .removeExistingAnchors])
    }

    func stop() {
        motionManager.stopDeviceMotionUpdates()
        session.pause()
        mailbox.withLock {
            $0.state = .off
            $0.camera = nil
            $0.voxelCapture = nil
            $0.tracking = nil
            $0.wantsVoxelCapture = false
        }
    }

    /// The lowest-resolution 60 fps format from the wide camera saves image
    /// processing power; ARKit tracks fine at that size.
    static func preferredVideoFormat() -> ARConfiguration.VideoFormat? {
        let formats = ARWorldTrackingConfiguration.supportedVideoFormats.filter {
            $0.framesPerSecond == 60 && $0.captureDeviceType == .builtInWideAngleCamera
        }
        return formats.min { a, b in
            a.imageResolution.width * a.imageResolution.height < b.imageResolution.width * b.imageResolution.height
        }
    }

    func setWantsCameraFrames(_ wants: Bool) {
        mailbox.withLock {
            $0.wantsCamera = wants
            if !wants { $0.camera = nil }
        }
    }

    /// Enables LiDAR (or scene-depth) capture for Minecraft. Reconfigures the
    /// running ARKit session when the flag changes. Does not reset tracking.
    func setWantsVoxelCapture(_ wants: Bool) {
        let changed = mailbox.withLock { box -> Bool in
            guard box.wantsVoxelCapture != wants else { return false }
            box.wantsVoxelCapture = wants
            if !wants { box.voxelCapture = nil }
            return true
        }
        guard changed else { return }
        applySessionConfiguration()
    }

    /// Newest ARKit pose, detected floor height, and camera image.
    func latest() -> (tracking: VRTrackingSample?, floorHeight: Float?, camera: VRCameraFrame?) {
        mailbox.withLock { ($0.tracking, $0.floorHeight, $0.camera) }
    }

    /// Newest depth-capable camera frame for voxel integration.
    func latestVoxelCapture() -> VRVoxelCaptureFrame? {
        mailbox.withLock { $0.voxelCapture }
    }

    /// Newest Core Motion sample.
    func pollMotion() -> VRMotionSample? {
        guard let motion = motionManager.deviceMotion else { return nil }
        let q = motion.attitude.quaternion
        let rate = motion.rotationRate
        return VRMotionSample(
            timestamp: motion.timestamp,
            attitude: simd_quatf(ix: Float(q.x), iy: Float(q.y), iz: Float(q.z), r: Float(q.w)).normalized,
            rotationRate: SIMD3(Float(rate.x), Float(rate.y), Float(rate.z))
        )
    }

    // MARK: - ARSessionDelegate

    func session(_ session: ARSession, didUpdate frame: ARFrame) {
        let camera = frame.camera
        let quality: VRTrackingSample.Quality
        if case .normal = camera.trackingState {
            quality = .normal
        } else if case .limited = camera.trackingState {
            quality = .limited
        } else {
            quality = .unavailable
        }
        let sample = VRTrackingSample(timestamp: frame.timestamp, worldFromCamera: camera.transform, quality: quality)
        let resolution = camera.imageResolution
        let depthData = frame.smoothedSceneDepth ?? frame.sceneDepth
        mailbox.withLock {
            $0.tracking = sample
            if case .starting = $0.state { $0.state = .running }
            if $0.wantsCamera {
                $0.camera = VRCameraFrame(
                    pixelBuffer: frame.capturedImage,
                    timestamp: frame.timestamp,
                    worldFromCamera: camera.transform,
                    intrinsics: camera.intrinsics,
                    imageWidth: Float(resolution.width),
                    imageHeight: Float(resolution.height)
                )
            }
            if $0.wantsVoxelCapture {
                $0.voxelCapture = VRVoxelCaptureFrame(
                    capturedImage: frame.capturedImage,
                    depthMap: depthData?.depthMap,
                    confidenceMap: depthData?.confidenceMap,
                    featurePoints: depthData == nil ? frame.rawFeaturePoints?.points : nil,
                    intrinsics: camera.intrinsics,
                    cameraTransform: camera.transform,
                    timestamp: frame.timestamp
                )
            }
        }
        if lookingForFloor { considerFloor(frame.anchors, cameraHeight: camera.transform.columns.3.y) }
    }

    func session(_ session: ARSession, didFailWithError error: Error) {
        mailbox.withLock {
            $0.state = .failed(error.localizedDescription)
            $0.tracking = nil
        }
    }

    func sessionWasInterrupted(_ session: ARSession) {
        mailbox.withLock { $0.tracking = nil }
    }

    func sessionShouldAttemptRelocalization(_ session: ARSession) -> Bool {
        true
    }

    /// Picks the floor from horizontal planes: one ARKit classifies as floor,
    /// or failing that the lowest large plane well below the head. Plane
    /// detection stops once a floor is found, to save power.
    private func considerFloor(_ anchors: [ARAnchor], cameraHeight: Float) {
        var best: Float?
        for anchor in anchors {
            guard let plane = anchor as? ARPlaneAnchor, plane.alignment == .horizontal else { continue }
            let height = plane.transform.columns.3.y
            let area = plane.planeExtent.width * plane.planeExtent.height
            var isFloor = false
            if ARPlaneAnchor.isClassificationSupported, case .floor = plane.classification {
                isFloor = area > 0.5
            } else {
                isFloor = area > 1.0 && height < cameraHeight - 0.9
            }
            if isFloor, best.map({ height < $0 }) ?? true { best = height }
        }
        guard let floor = best else { return }
        lookingForFloor = false
        mailbox.withLock { $0.floorHeight = floor }
        applySessionConfiguration()
    }

    /// Applies plane detection and scene-depth semantics without resetting
    /// the world origin, so voxels stay aligned with the room. Always hops
    /// to the delegate queue so `session.run` is not called from `didUpdate`.
    private func applySessionConfiguration() {
        delegateQueue.async { [weak self] in
            self?.runSessionConfiguration()
        }
    }

    private func runSessionConfiguration() {
        guard let configuration, cameraState != .off else { return }
        let wantsDepth = mailbox.withLock { $0.wantsVoxelCapture }
        configuration.frameSemantics.remove(.smoothedSceneDepth)
        configuration.frameSemantics.remove(.sceneDepth)
        if wantsDepth {
            if ARWorldTrackingConfiguration.supportsFrameSemantics(.smoothedSceneDepth) {
                configuration.frameSemantics.insert(.smoothedSceneDepth)
            } else if ARWorldTrackingConfiguration.supportsFrameSemantics(.sceneDepth) {
                configuration.frameSemantics.insert(.sceneDepth)
            }
        }
        if !lookingForFloor {
            configuration.planeDetection = []
        }
        session.run(configuration, options: [])
    }
}
