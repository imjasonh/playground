import AVFoundation
import CoreImage
import QuartzCore
import UIKit

/// Live camera that dyes hair on device. Frames are not uploaded.
///
/// The preview uses Vision person segmentation limited to the scalp. A still
/// photo uses `AVSemanticSegmentationMatte.hair` when the device offers it.
final class HairColorSession: NSObject, ObservableObject {
    enum RunState: Equatable {
        case idle
        case requestingPermission
        case running
        case noCamera
        case permissionDenied
        case failed(String)
    }

    @Published private(set) var runState: RunState = .idle
    @Published private(set) var statusMessage = "Hair tint stays on this device."
    @Published private(set) var previewImage: UIImage?
    @Published private(set) var previewImageSize: CGSize = .zero
    @Published private(set) var stillImage: UIImage?
    @Published private(set) var usingFrontCamera = true
    @Published private(set) var dye: HairDye = .defaultDye
    @Published private(set) var strength: CGFloat = 0.85
    @Published private(set) var showsMask = false
    @Published private(set) var canCapture = false
    @Published private(set) var isCapturing = false

    private let session = AVCaptureSession()
    private let videoOutput = AVCaptureVideoDataOutput()
    private let photoOutput = AVCapturePhotoOutput()
    private let sessionQueue = DispatchQueue(label: "hair-color.session")
    private let outputQueue = DispatchQueue(label: "hair-color.output", qos: .userInitiated)
    private let previewContext = CIContext(options: [.useSoftwareRenderer: false])
    private let requests = HairFrameProcessor.makeRequests()

    private let stateLock = NSLock()
    private var cameraPosition: AVCaptureDevice.Position = .front
    private var deviceOrientation: UIDeviceOrientation = .portrait
    private var dyeForProcessing: HairDye = .defaultDye
    private var strengthForProcessing: CGFloat = 0.85
    private var showsMaskForProcessing = false
    private var showingStill = false
    private var sawFace = false
    private var capturingPhoto = false
    private var orientationObserver: NSObjectProtocol?

    private let maskLock = NSLock()
    private var latestMask: CIImage?
    private var lastSegmentTime: CFTimeInterval = 0
    private var isSegmenting = false
    private let segmentInterval: CFTimeInterval = 0.12
    private let previewMaxEdge: CGFloat = 960

    func start() {
        switch runState {
        case .running, .requestingPermission:
            return
        default:
            break
        }

        runState = .requestingPermission
        statusMessage = "Requesting camera access…"
        beginOrientationUpdates()

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
        endOrientationUpdates()
        sessionQueue.async { [session] in
            if session.isRunning {
                session.stopRunning()
            }
        }
        clearMask()
        DispatchQueue.main.async { [weak self] in
            guard let self else { return }
            self.previewImage = nil
            self.previewImageSize = .zero
            self.stillImage = nil
            self.canCapture = false
            self.isCapturing = false
            self.stateLock.lock()
            self.showingStill = false
            self.stateLock.unlock()
            if self.runState == .running {
                self.runState = .idle
                self.statusMessage = "Stopped. Frames never left this device."
            }
        }
    }

    func setDye(_ dye: HairDye) {
        self.dye = dye
        stateLock.lock()
        dyeForProcessing = dye
        stateLock.unlock()
        refreshRunningStatus()
    }

    func setStrength(_ value: CGFloat) {
        let clamped = min(max(value, 0), 1)
        strength = clamped
        stateLock.lock()
        strengthForProcessing = clamped
        stateLock.unlock()
    }

    func setShowsMask(_ shows: Bool) {
        showsMask = shows
        stateLock.lock()
        showsMaskForProcessing = shows
        stateLock.unlock()
    }

    func flipCamera() {
        sessionQueue.async { [weak self] in
            guard let self else { return }
            let current = self.currentOrientationAndCamera().1
            let next: AVCaptureDevice.Position = current == .back ? .front : .back
            do {
                try self.configureSession(position: next)
                self.enableHairMatteIfAvailable()
                self.clearMask()
                DispatchQueue.main.async {
                    self.usingFrontCamera = next == .front
                    self.refreshRunningStatus()
                }
            } catch {
                DispatchQueue.main.async {
                    self.statusMessage = error.localizedDescription
                }
            }
        }
    }

    func capture() {
        sessionQueue.async { [weak self] in
            guard let self else { return }
            self.stateLock.lock()
            let busy = self.capturingPhoto
            if !busy {
                self.capturingPhoto = true
            }
            self.stateLock.unlock()
            guard !busy else { return }
            guard self.session.outputs.contains(where: { $0 === self.photoOutput }) else {
                self.finishCaptureAttempt(message: "This device can't take a photo from Hair Color.")
                return
            }
            self.orientPhotoConnection()
            let settings = AVCapturePhotoSettings()
            if self.photoOutput.enabledSemanticSegmentationMatteTypes.contains(.hair) {
                settings.enabledSemanticSegmentationMatteTypes = [.hair]
            }
            DispatchQueue.main.async { self.isCapturing = true }
            self.photoOutput.capturePhoto(with: settings, delegate: self)
        }
    }

    func retake() {
        stateLock.lock()
        showingStill = false
        stateLock.unlock()
        stillImage = nil
        refreshRunningStatus()
    }

    // MARK: - Configuration

    private func configureAndStart() {
        sessionQueue.async { [weak self] in
            guard let self else { return }
            do {
                try self.configureSession(position: .front)
                self.enableHairMatteIfAvailable()
                self.session.startRunning()
                let captureReady = self.session.outputs.contains(where: { $0 === self.photoOutput })
                let startedOnFront = self.currentOrientationAndCamera().1 == .front
                DispatchQueue.main.async {
                    self.usingFrontCamera = startedOnFront
                    self.canCapture = captureReady
                    self.runState = .running
                    self.refreshRunningStatus()
                }
            } catch let error as HairColorError where error == .noCamera {
                DispatchQueue.main.async {
                    self.runState = .noCamera
                    self.statusMessage = "No camera on this device. The Simulator has none."
                }
            } catch {
                DispatchQueue.main.async {
                    self.runState = .failed(error.localizedDescription)
                    self.statusMessage = error.localizedDescription
                }
            }
        }
    }

    private func configureSession(position: AVCaptureDevice.Position) throws {
        session.beginConfiguration()
        defer { session.commitConfiguration() }

        if session.canSetSessionPreset(.photo) {
            session.sessionPreset = .photo
        } else {
            session.sessionPreset = .high
        }

        for input in session.inputs {
            session.removeInput(input)
        }
        for output in session.outputs {
            session.removeOutput(output)
        }

        guard let device = Self.camera(for: position) else {
            throw HairColorError.noCamera
        }
        let input = try AVCaptureDeviceInput(device: device)
        guard session.canAddInput(input) else {
            throw HairColorError.cannotAddInput
        }
        session.addInput(input)

        videoOutput.alwaysDiscardsLateVideoFrames = true
        videoOutput.videoSettings = [
            kCVPixelBufferPixelFormatTypeKey as String: kCVPixelFormatType_32BGRA,
        ]
        guard session.canAddOutput(videoOutput) else {
            throw HairColorError.cannotAddOutput
        }
        session.addOutput(videoOutput)
        videoOutput.setSampleBufferDelegate(self, queue: outputQueue)
        disableBufferMirroring()

        if session.canAddOutput(photoOutput) {
            session.addOutput(photoOutput)
        }

        stateLock.lock()
        cameraPosition = device.position
        stateLock.unlock()
    }

    /// Hair mattes can be queried only after the photo output is committed.
    private func enableHairMatteIfAvailable() {
        guard session.outputs.contains(where: { $0 === photoOutput }) else { return }
        session.beginConfiguration()
        if photoOutput.availableSemanticSegmentationMatteTypes.contains(.hair) {
            photoOutput.enabledSemanticSegmentationMatteTypes = [.hair]
        }
        session.commitConfiguration()
    }

    private func orientPhotoConnection() {
        guard let connection = photoOutput.connection(with: .video) else { return }
        let (orientation, position) = currentOrientationAndCamera()
        let angle = HairColorOrientation.photoRotationAngle(for: orientation)
        if connection.isVideoRotationAngleSupported(angle) {
            connection.videoRotationAngle = angle
        }
        if connection.isVideoMirroringSupported {
            connection.automaticallyAdjustsVideoMirroring = false
            connection.isVideoMirrored = position == .front
        }
    }

    private func disableBufferMirroring() {
        guard let connection = videoOutput.connection(with: .video) else { return }
        if connection.isVideoMirroringSupported {
            connection.automaticallyAdjustsVideoMirroring = false
            connection.isVideoMirrored = false
        }
    }

    private static func camera(for position: AVCaptureDevice.Position) -> AVCaptureDevice? {
        AVCaptureDevice.default(.builtInWideAngleCamera, for: .video, position: position)
            ?? AVCaptureDevice.default(for: .video)
    }

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

    private func beginOrientationUpdates() {
        UIDevice.current.beginGeneratingDeviceOrientationNotifications()
        let initial = Self.resolvedDeviceOrientation(UIDevice.current.orientation)
        stateLock.lock()
        deviceOrientation = initial
        stateLock.unlock()
        orientationObserver = NotificationCenter.default.addObserver(
            forName: UIDevice.orientationDidChangeNotification,
            object: nil,
            queue: .main
        ) { [weak self] _ in
            guard let self else { return }
            let next = Self.resolvedDeviceOrientation(UIDevice.current.orientation)
            self.stateLock.lock()
            self.deviceOrientation = next
            self.stateLock.unlock()
        }
    }

    private func endOrientationUpdates() {
        if let orientationObserver {
            NotificationCenter.default.removeObserver(orientationObserver)
            self.orientationObserver = nil
        }
        UIDevice.current.endGeneratingDeviceOrientationNotifications()
    }

    private static func resolvedDeviceOrientation(_ raw: UIDeviceOrientation) -> UIDeviceOrientation {
        switch raw {
        case .portrait, .portraitUpsideDown, .landscapeLeft, .landscapeRight:
            return raw
        default:
            if let scene = UIApplication.shared.connectedScenes
                .compactMap({ $0 as? UIWindowScene })
                .first
            {
                switch scene.effectiveGeometry.interfaceOrientation {
                case .portrait: return .portrait
                case .portraitUpsideDown: return .portraitUpsideDown
                case .landscapeLeft: return .landscapeLeft
                case .landscapeRight: return .landscapeRight
                default: break
                }
            }
            return .portrait
        }
    }

    private func currentOrientationAndCamera() -> (UIDeviceOrientation, AVCaptureDevice.Position) {
        stateLock.lock()
        defer { stateLock.unlock() }
        return (deviceOrientation, cameraPosition)
    }

    private func processingSettings() -> (HairDye, CGFloat, Bool, Bool) {
        stateLock.lock()
        defer { stateLock.unlock() }
        return (dyeForProcessing, strengthForProcessing, showsMaskForProcessing, showingStill)
    }

    private func clearMask() {
        maskLock.lock()
        latestMask = nil
        maskLock.unlock()
        stateLock.lock()
        sawFace = false
        stateLock.unlock()
    }

    private func storeMask(_ mask: CIImage?) {
        maskLock.lock()
        latestMask = mask
        maskLock.unlock()
        stateLock.lock()
        sawFace = mask != nil
        stateLock.unlock()
    }

    private func currentMask() -> CIImage? {
        maskLock.lock()
        defer { maskLock.unlock() }
        return latestMask
    }

    private func refreshRunningStatus() {
        guard runState == .running else { return }
        stateLock.lock()
        let face = sawFace
        let still = showingStill
        stateLock.unlock()
        if still { return }
        if face {
            statusMessage = "\(dye.name) · \(usingFrontCamera ? "Front" : "Rear") camera"
        } else {
            statusMessage = "Looking for a face · \(dye.name)"
        }
    }

    private func finishCaptureAttempt(message: String) {
        stateLock.lock()
        capturingPhoto = false
        stateLock.unlock()
        DispatchQueue.main.async {
            self.isCapturing = false
            self.statusMessage = message
        }
    }
}

enum HairColorError: Error, Equatable, LocalizedError {
    case noCamera
    case cannotAddInput
    case cannotAddOutput

    var errorDescription: String? {
        switch self {
        case .noCamera:
            return "No camera is available."
        case .cannotAddInput:
            return "Couldn't add the camera input."
        case .cannotAddOutput:
            return "Couldn't add the camera output."
        }
    }
}

extension HairColorSession: AVCaptureVideoDataOutputSampleBufferDelegate {
    func captureOutput(
        _ output: AVCaptureOutput,
        didOutput sampleBuffer: CMSampleBuffer,
        from connection: AVCaptureConnection
    ) {
        let (dye, strength, showsMask, showingStill) = processingSettings()
        if showingStill { return }
        guard let pixelBuffer = CMSampleBufferGetImageBuffer(sampleBuffer) else { return }

        let (deviceOrientation, position) = currentOrientationAndCamera()
        let orientation = HairColorOrientation.visionOrientation(
            deviceOrientation: deviceOrientation,
            cameraPosition: position
        )
        let upright = HairColorOrientation.uprightCIImage(from: pixelBuffer, orientation: orientation)
        let preview = HairColorOrientation.downscaled(upright, maxEdge: previewMaxEdge)

        let now = CACurrentMediaTime()
        if !isSegmenting, (now - lastSegmentTime) >= segmentInterval {
            isSegmenting = true
            lastSegmentTime = now
            let mask = HairFrameProcessor.hairMask(
                for: preview,
                personRequest: requests.person,
                faceRequest: requests.face
            )
            storeMask(mask)
            isSegmenting = false
            DispatchQueue.main.async { [weak self] in
                self?.refreshRunningStatus()
            }
        }

        let composited = composite(preview, dye: dye, strength: strength, showsMask: showsMask)
        guard let image = HairColorCompositor.render(composited, context: previewContext) else { return }
        let size = preview.extent.size
        DispatchQueue.main.async { [weak self] in
            guard let self, self.stillImage == nil else { return }
            self.previewImage = image
            self.previewImageSize = size
        }
    }

    private func composite(_ image: CIImage, dye: HairDye, strength: CGFloat, showsMask: Bool) -> CIImage {
        guard let mask = currentMask() else { return image }
        if showsMask {
            return HairColorCompositor.showMask(image: image, mask: mask)
        }
        let radius = max(1.5, image.extent.width * 0.012)
        return HairColorCompositor.apply(
            image: image,
            mask: mask,
            dye: dye,
            strength: strength,
            blurRadius: radius
        )
    }
}

extension HairColorSession: AVCapturePhotoCaptureDelegate {
    func photoOutput(
        _ output: AVCapturePhotoOutput,
        didFinishProcessingPhoto photo: AVCapturePhoto,
        error: Error?
    ) {
        if let error {
            finishCaptureAttempt(message: error.localizedDescription)
            return
        }
        // Copy before returning. The photo's buffers are only valid in this callback.
        guard let data = photo.fileDataRepresentation() else {
            finishCaptureAttempt(message: "Couldn't read the photo.")
            return
        }
        let metadata = photo.metadata
        let matte: CIImage?
        if let hairMatte = photo.semanticSegmentationMatte(for: .hair) {
            let buffer = HairMaskImage.detached(hairMatte.mattingImage) ?? hairMatte.mattingImage
            matte = CIImage(cvPixelBuffer: buffer)
        } else {
            matte = nil
        }
        outputQueue.async { [weak self] in
            self?.publishStill(data: data, metadata: metadata, matte: matte)
        }
    }

    func photoOutput(
        _ output: AVCapturePhotoOutput,
        didFinishCaptureFor resolvedSettings: AVCaptureResolvedPhotoSettings,
        error: Error?
    ) {
        stateLock.lock()
        capturingPhoto = false
        stateLock.unlock()
        DispatchQueue.main.async { [weak self] in
            self?.isCapturing = false
        }
        if let error {
            DispatchQueue.main.async { [weak self] in
                self?.statusMessage = error.localizedDescription
            }
        }
    }

    private func publishStill(data: Data, metadata: [String: Any], matte: CIImage?) {
        guard let source = CIImage(data: data) else {
            DispatchQueue.main.async { [weak self] in
                self?.statusMessage = "Couldn't read the photo."
            }
            return
        }
        let image = HairColorOrientation.rebase(source)
        let settings = processingSettings()
        let orientation = HairPhotoAlignment.orientation(from: metadata)
        let usedHairMatte: Bool
        let mask: CIImage?
        if let matte {
            mask = HairPhotoAlignment.matching(matte, to: image, orientation: orientation)
            usedHairMatte = true
        } else {
            let small = HairColorOrientation.downscaled(image, maxEdge: previewMaxEdge)
            mask = HairFrameProcessor.hairMask(
                for: small,
                personRequest: requests.person,
                faceRequest: requests.face
            )
            usedHairMatte = false
        }

        let composited: CIImage
        if let mask {
            if settings.2 {
                composited = HairColorCompositor.showMask(image: image, mask: mask)
            } else {
                composited = HairColorCompositor.apply(
                    image: image,
                    mask: mask,
                    dye: settings.0,
                    strength: settings.1,
                    blurRadius: max(2, image.extent.width * 0.008)
                )
            }
        } else {
            composited = image
        }

        guard let rendered = HairColorCompositor.render(composited, context: previewContext) else { return }
        stateLock.lock()
        showingStill = true
        stateLock.unlock()
        let dyeName = settings.0.name
        DispatchQueue.main.async { [weak self] in
            guard let self else { return }
            self.stillImage = rendered
            self.previewImageSize = image.extent.size
            if usedHairMatte {
                self.statusMessage = "Hair matte · \(dyeName)"
            } else if mask == nil {
                self.statusMessage = "No hair found · \(dyeName)"
            } else {
                self.statusMessage = "Snapshot · \(dyeName)"
            }
        }
    }
}
