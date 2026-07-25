import AVFoundation
import CoreMotion
import CoreVideo
import UIKit

/// Dual-wide MultiCam session: live preview + one-shot stereo stills when level.
final class ViewMasterStereoSession: NSObject, ObservableObject {
    enum RunState: Equatable {
        case idle
        case requestingPermission
        case running
        case unsupported
        case permissionDenied
        case failed(String)
    }

    enum PreviewMode: String, CaseIterable, Identifiable {
        case sideBySide
        case wigglegram

        var id: String { rawValue }

        var title: String {
            switch self {
            case .sideBySide: return "Left / Right"
            case .wigglegram: return "Wigglegram"
            }
        }
    }

    @Published private(set) var runState: RunState = .idle
    @Published private(set) var statusMessage = "Hold landscape and level, then capture a stereo pair."
    @Published private(set) var readiness = StereoCaptureGate.Readiness(
        isLandscape: false,
        isLevel: false,
        orientation: .flatOrUnknown,
        blockingReason: "Starting…"
    )
    @Published private(set) var previewImage: UIImage?
    @Published private(set) var capturedPair: StereoPairAligner.Pair?
    @Published var previewMode: PreviewMode = .sideBySide

    private let multiSession = AVCaptureMultiCamSession()
    private let wideOutput = AVCaptureVideoDataOutput()
    private let ultraWideOutput = AVCaptureVideoDataOutput()
    private var synchronizer: AVCaptureDataOutputSynchronizer?
    private let sessionQueue = DispatchQueue(label: "viewmaster-stereo.session")
    private let outputQueue = DispatchQueue(label: "viewmaster-stereo.output", qos: .userInitiated)
    private let motion = CMMotionManager()
    private let motionQueue = OperationQueue()

    private let frameLock = NSLock()
    private var captureRequested = false
    private var currentOrientation: StereoCaptureGate.Orientation = .flatOrUnknown
    private weak var wideConnection: AVCaptureConnection?
    private weak var ultraConnection: AVCaptureConnection?

    var canCapture: Bool {
        runState == .running && readiness.canCapture && capturedPair == nil
    }

    func start() {
        switch runState {
        case .running, .requestingPermission:
            return
        default:
            break
        }

        runState = .requestingPermission
        statusMessage = "Requesting camera access…"

        Task { @MainActor in
            let granted = await Self.requestCameraAccess()
            guard granted else {
                self.runState = .permissionDenied
                self.statusMessage = "Camera access is required. Enable it in Settings."
                return
            }
            self.configureAndStart()
        }
    }

    func stop() {
        stopMotion()
        let sync = synchronizer
        synchronizer = nil
        sessionQueue.async { [multiSession] in
            _ = sync
            if multiSession.isRunning {
                multiSession.stopRunning()
            }
        }
        DispatchQueue.main.async { [weak self] in
            guard let self else { return }
            self.previewImage = nil
            if self.runState == .running {
                self.runState = .idle
                self.statusMessage = "Stopped."
            }
        }
    }

    func capture() {
        guard canCapture else { return }
        frameLock.lock()
        captureRequested = true
        frameLock.unlock()
        statusMessage = "Capturing stereo pair…"
    }

    func clearCapture() {
        capturedPair = nil
        statusMessage = readiness.canCapture
            ? "Ready — tap Capture for a stereo pair."
            : readiness.blockingReason
    }

    // MARK: - Configuration

    private func configureAndStart() {
        sessionQueue.async { [weak self] in
            guard let self else { return }
            do {
                try self.configureSession()
                self.multiSession.startRunning()
                DispatchQueue.main.async {
                    self.runState = .running
                    self.statusMessage = "Hold landscape and level, then capture."
                    self.startMotion()
                }
            } catch let error as StereoSessionError {
                DispatchQueue.main.async {
                    self.runState = error == .unsupported ? .unsupported : .failed(error.localizedDescription)
                    self.statusMessage = error.localizedDescription
                }
            } catch {
                DispatchQueue.main.async {
                    self.runState = .failed(error.localizedDescription)
                    self.statusMessage = error.localizedDescription
                }
            }
        }
    }

    private func configureSession() throws {
        guard AVCaptureMultiCamSession.isMultiCamSupported else {
            throw StereoSessionError.unsupported
        }
        guard let device = AVCaptureDevice.default(.builtInDualWideCamera, for: .video, position: .back)
        else {
            throw StereoSessionError.unsupported
        }

        multiSession.beginConfiguration()
        defer { multiSession.commitConfiguration() }

        for input in multiSession.inputs {
            multiSession.removeInput(input)
        }
        for output in multiSession.outputs {
            multiSession.removeOutput(output)
        }

        try Self.selectMultiCamFormat(for: device)

        let input = try AVCaptureDeviceInput(device: device)
        guard multiSession.canAddInput(input) else {
            throw StereoSessionError.cannotConfigure
        }
        multiSession.addInputWithNoConnections(input)

        guard
            let widePort = input.ports(
                for: .video,
                sourceDeviceType: .builtInWideAngleCamera,
                sourceDevicePosition: .back
            ).first,
            let ultraPort = input.ports(
                for: .video,
                sourceDeviceType: .builtInUltraWideCamera,
                sourceDevicePosition: .back
            ).first
        else {
            throw StereoSessionError.unsupported
        }

        wideOutput.alwaysDiscardsLateVideoFrames = true
        wideOutput.videoSettings = [
            kCVPixelBufferPixelFormatTypeKey as String: kCVPixelFormatType_32BGRA,
        ]
        ultraWideOutput.alwaysDiscardsLateVideoFrames = true
        ultraWideOutput.videoSettings = [
            kCVPixelBufferPixelFormatTypeKey as String: kCVPixelFormatType_32BGRA,
        ]

        guard multiSession.canAddOutput(wideOutput), multiSession.canAddOutput(ultraWideOutput) else {
            throw StereoSessionError.cannotConfigure
        }
        multiSession.addOutputWithNoConnections(wideOutput)
        multiSession.addOutputWithNoConnections(ultraWideOutput)

        let wideConnection = AVCaptureConnection(inputPorts: [widePort], output: wideOutput)
        let ultraConnection = AVCaptureConnection(inputPorts: [ultraPort], output: ultraWideOutput)
        guard multiSession.canAddConnection(wideConnection),
              multiSession.canAddConnection(ultraConnection)
        else {
            throw StereoSessionError.cannotConfigure
        }
        multiSession.addConnection(wideConnection)
        multiSession.addConnection(ultraConnection)
        self.wideConnection = wideConnection
        self.ultraConnection = ultraConnection
        Self.apply(videoOrientation: .landscapeRight, to: wideConnection, ultraConnection)

        if multiSession.hardwareCost > 1.0 {
            throw StereoSessionError.unsupported
        }

        let synchronizer = AVCaptureDataOutputSynchronizer(dataOutputs: [wideOutput, ultraWideOutput])
        synchronizer.setDelegate(self, queue: outputQueue)
        self.synchronizer = synchronizer
    }

    private static func selectMultiCamFormat(for device: AVCaptureDevice) throws {
        let candidates = device.formats.filter(\.isMultiCamSupported)
        guard !candidates.isEmpty else {
            throw StereoSessionError.unsupported
        }

        // Prefer a modest 1080p-class format to stay under MultiCam hardware cost.
        let preferred = candidates.max { a, b in
            let da = CMVideoFormatDescriptionGetDimensions(a.formatDescription)
            let db = CMVideoFormatDescriptionGetDimensions(b.formatDescription)
            let sa = score(width: Int(da.width), height: Int(da.height))
            let sb = score(width: Int(db.width), height: Int(db.height))
            return sa < sb
        }

        guard let format = preferred else {
            throw StereoSessionError.unsupported
        }

        try device.lockForConfiguration()
        device.activeFormat = format
        device.activeVideoMinFrameDuration = CMTime(value: 1, timescale: 30)
        device.activeVideoMaxFrameDuration = CMTime(value: 1, timescale: 30)
        device.unlockForConfiguration()
    }

    private static func score(width: Int, height: Int) -> Int {
        let pixels = width * height
        let target = 1920 * 1080
        return -abs(pixels - target)
    }

    // MARK: - Motion

    private func startMotion() {
        guard motion.isDeviceMotionAvailable else {
            readiness = StereoCaptureGate.Readiness(
                isLandscape: false,
                isLevel: false,
                orientation: .flatOrUnknown,
                blockingReason: "Motion sensors unavailable."
            )
            return
        }
        motion.deviceMotionUpdateInterval = 1.0 / 30.0
        motionQueue.name = "viewmaster-stereo.motion"
        motionQueue.maxConcurrentOperationCount = 1
        motion.startDeviceMotionUpdates(to: motionQueue) { [weak self] data, _ in
            guard let self, let gravity = data?.gravity else { return }
            let next = StereoCaptureGate.evaluate(
                gravityX: gravity.x,
                gravityY: gravity.y,
                gravityZ: gravity.z
            )
            DispatchQueue.main.async {
                let orientationChanged = self.currentOrientation != next.orientation
                self.currentOrientation = next.orientation
                self.readiness = next
                if orientationChanged {
                    self.updateVideoOrientation(for: next.orientation)
                }
                if self.capturedPair == nil {
                    self.statusMessage = next.canCapture
                        ? "Ready — tap Capture for a stereo pair."
                        : next.blockingReason
                }
            }
        }
    }

    private func stopMotion() {
        motion.stopDeviceMotionUpdates()
    }

    private func updateVideoOrientation(for orientation: StereoCaptureGate.Orientation) {
        let videoOrientation: AVCaptureVideoOrientation
        switch orientation {
        case .landscapeLeft:
            videoOrientation = .landscapeLeft
        case .landscapeRight:
            videoOrientation = .landscapeRight
        case .portrait, .flatOrUnknown:
            return
        }
        let wide = wideConnection
        let ultra = ultraConnection
        sessionQueue.async {
            Self.apply(videoOrientation: videoOrientation, to: wide, ultra)
        }
    }

    private static func apply(
        videoOrientation: AVCaptureVideoOrientation,
        to wide: AVCaptureConnection?,
        _ ultra: AVCaptureConnection?
    ) {
        if let wide, wide.isVideoOrientationSupported {
            wide.videoOrientation = videoOrientation
        }
        if let ultra, ultra.isVideoOrientationSupported {
            ultra.videoOrientation = videoOrientation
        }
    }

    // MARK: - Permissions / conversion

    @MainActor
    private static func requestCameraAccess() async -> Bool {
        switch AVCaptureDevice.authorizationStatus(for: .video) {
        case .authorized:
            return true
        case .notDetermined:
            return await AVCaptureDevice.requestAccess(for: .video)
        default:
            return false
        }
    }

    private static func image(from pixelBuffer: CVPixelBuffer) -> UIImage? {
        let ciImage = CIImage(cvPixelBuffer: pixelBuffer)
        let context = CIContext(options: [.useSoftwareRenderer: false])
        guard let cgImage = context.createCGImage(ciImage, from: ciImage.extent) else {
            return nil
        }
        return UIImage(cgImage: cgImage, scale: 1, orientation: .up)
    }
}

// MARK: - Synchronizer

extension ViewMasterStereoSession: AVCaptureDataOutputSynchronizerDelegate {
    func dataOutputSynchronizer(
        _ synchronizer: AVCaptureDataOutputSynchronizer,
        didOutput synchronizedDataCollection: AVCaptureSynchronizedDataCollection
    ) {
        let wideData = synchronizedDataCollection.synchronizedData(for: wideOutput)
            as? AVCaptureSynchronizedSampleBufferData
        let ultraData = synchronizedDataCollection.synchronizedData(for: ultraWideOutput)
            as? AVCaptureSynchronizedSampleBufferData

        guard
            let wideBuffer = wideData?.sampleBuffer,
            let ultraBuffer = ultraData?.sampleBuffer,
            let widePixels = CMSampleBufferGetImageBuffer(wideBuffer),
            let ultraPixels = CMSampleBufferGetImageBuffer(ultraBuffer)
        else {
            return
        }

        if let preview = Self.image(from: widePixels) {
            DispatchQueue.main.async { [weak self] in
                guard let self, self.capturedPair == nil else { return }
                self.previewImage = preview
            }
        }

        frameLock.lock()
        let shouldCapture = captureRequested
        if shouldCapture {
            captureRequested = false
        }
        frameLock.unlock()

        guard shouldCapture else { return }

        // Retain copies — pixel buffers from the session are recycled.
        guard
            let wideCopy = Self.copyPixelBuffer(widePixels),
            let ultraCopy = Self.copyPixelBuffer(ultraPixels),
            let wideImage = Self.image(from: wideCopy),
            let ultraImage = Self.image(from: ultraCopy)
        else {
            DispatchQueue.main.async { [weak self] in
                self?.statusMessage = "Capture failed — try again."
            }
            return
        }

        let swap = StereoCaptureGate.shouldSwapEyes(for: currentOrientation)
        guard let pair = StereoPairAligner.makePair(
            wide: wideImage,
            ultraWide: ultraImage,
            swapEyes: swap
        ) else {
            DispatchQueue.main.async { [weak self] in
                self?.statusMessage = "Could not align stereo pair."
            }
            return
        }

        DispatchQueue.main.async { [weak self] in
            guard let self else { return }
            self.capturedPair = pair
            self.previewMode = .sideBySide
            self.statusMessage = "Stereo pair captured — preview left/right or wigglegram."
        }
    }

    private static func copyPixelBuffer(_ source: CVPixelBuffer) -> CVPixelBuffer? {
        let width = CVPixelBufferGetWidth(source)
        let height = CVPixelBufferGetHeight(source)
        var copy: CVPixelBuffer?
        let status = CVPixelBufferCreate(
            kCFAllocatorDefault,
            width,
            height,
            CVPixelBufferGetPixelFormatType(source),
            [
                kCVPixelBufferIOSurfacePropertiesKey: [:] as CFDictionary,
            ] as CFDictionary,
            &copy
        )
        guard status == kCVReturnSuccess, let destination = copy else { return nil }

        CVPixelBufferLockBaseAddress(source, .readOnly)
        CVPixelBufferLockBaseAddress(destination, [])
        defer {
            CVPixelBufferUnlockBaseAddress(destination, [])
            CVPixelBufferUnlockBaseAddress(source, .readOnly)
        }

        let planeCount = CVPixelBufferGetPlaneCount(source)
        if planeCount == 0 {
            guard
                let src = CVPixelBufferGetBaseAddress(source),
                let dst = CVPixelBufferGetBaseAddress(destination)
            else { return nil }
            let srcBytes = CVPixelBufferGetBytesPerRow(source)
            let dstBytes = CVPixelBufferGetBytesPerRow(destination)
            let rowBytes = min(srcBytes, dstBytes)
            for row in 0..<height {
                memcpy(dst.advanced(by: row * dstBytes), src.advanced(by: row * srcBytes), rowBytes)
            }
        } else {
            for plane in 0..<planeCount {
                guard
                    let src = CVPixelBufferGetBaseAddressOfPlane(source, plane),
                    let dst = CVPixelBufferGetBaseAddressOfPlane(destination, plane)
                else { continue }
                let planeHeight = CVPixelBufferGetHeightOfPlane(source, plane)
                let srcBytes = CVPixelBufferGetBytesPerRowOfPlane(source, plane)
                let dstBytes = CVPixelBufferGetBytesPerRowOfPlane(destination, plane)
                let rowBytes = min(srcBytes, dstBytes)
                for row in 0..<planeHeight {
                    memcpy(dst.advanced(by: row * dstBytes), src.advanced(by: row * srcBytes), rowBytes)
                }
            }
        }
        return destination
    }
}

private enum StereoSessionError: LocalizedError, Equatable {
    case unsupported
    case cannotConfigure

    var errorDescription: String? {
        switch self {
        case .unsupported:
            return "Dual-wide MultiCam stereo needs a rear ultra-wide + wide camera (e.g. recent iPhone). Simulator can’t capture pairs."
        case .cannotConfigure:
            return "Could not configure the dual-camera capture session."
        }
    }
}
