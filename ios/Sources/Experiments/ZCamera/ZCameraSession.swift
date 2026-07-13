import AVFoundation
import CoreVideo
import UIKit

/// Live TrueDepth / dual-camera session that publishes z-band-masked preview frames.
final class ZCameraSession: NSObject, ObservableObject {
    enum RunState: Equatable {
        case idle
        case requestingPermission
        case running
        case noDepthCamera
        case permissionDenied
        case failed(String)
    }

    @Published private(set) var runState: RunState = .idle
    @Published private(set) var statusMessage = "Depth band: only pixels inside near…far stay visible."
    @Published private(set) var previewImage: UIImage?
    @Published private(set) var usingFrontCamera = false
    @Published private(set) var band: ZDepthBand = .open
    @Published private(set) var showDepthOverlay = false

    private let session = AVCaptureSession()
    private let videoOutput = AVCaptureVideoDataOutput()
    private let depthOutput = AVCaptureDepthDataOutput()
    private var synchronizer: AVCaptureDataOutputSynchronizer?
    private let sessionQueue = DispatchQueue(label: "z-camera.session")
    private let outputQueue = DispatchQueue(label: "z-camera.output", qos: .userInitiated)

    private let bandLock = NSLock()
    private var bandForProcessing = ZDepthBand.open
    private var overlayForProcessing = false

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
        let sync = synchronizer
        synchronizer = nil
        sessionQueue.async { [session] in
            _ = sync
            if session.isRunning {
                session.stopRunning()
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

    func updateBand(_ band: ZDepthBand) {
        let clamped = band.clamped()
        self.band = clamped
        bandLock.lock()
        bandForProcessing = clamped
        bandLock.unlock()
    }

    func updateShowDepthOverlay(_ enabled: Bool) {
        showDepthOverlay = enabled
        bandLock.lock()
        overlayForProcessing = enabled
        bandLock.unlock()
    }

    // MARK: - Configuration

    private func configureAndStart() {
        let initialBand = band.clamped()
        let initialOverlay = showDepthOverlay
        sessionQueue.async { [weak self] in
            guard let self else { return }
            do {
                let device = try self.configureSession(
                    initialBand: initialBand,
                    initialOverlay: initialOverlay
                )
                self.session.startRunning()
                DispatchQueue.main.async {
                    self.usingFrontCamera = device.position == .front
                    self.runState = .running
                    self.statusMessage = device.position == .front
                        ? "TrueDepth band active — slide near & far."
                        : "Depth band active — slide near & far."
                }
            } catch let error as ZCameraError where error == .noDepthCamera {
                DispatchQueue.main.async {
                    self.runState = .noDepthCamera
                    self.statusMessage = "No depth camera on this device. Try an iPhone with TrueDepth or a dual/LiDAR rear camera."
                }
            } catch {
                DispatchQueue.main.async {
                    self.runState = .failed(error.localizedDescription)
                    self.statusMessage = error.localizedDescription
                }
            }
        }
    }

    private func configureSession(
        initialBand: ZDepthBand,
        initialOverlay: Bool
    ) throws -> AVCaptureDevice {
        session.beginConfiguration()
        defer { session.commitConfiguration() }

        for input in session.inputs {
            session.removeInput(input)
        }
        for output in session.outputs {
            session.removeOutput(output)
        }

        guard let device = Self.preferredDepthDevice() else {
            throw ZCameraError.noDepthCamera
        }

        try Self.selectBestCaptureFormat(for: device)

        let input = try AVCaptureDeviceInput(device: device)
        guard session.canAddInput(input) else {
            throw ZCameraError.cannotAddInput
        }
        session.addInput(input)

        videoOutput.alwaysDiscardsLateVideoFrames = true
        videoOutput.videoSettings = [
            kCVPixelBufferPixelFormatTypeKey as String: kCVPixelFormatType_32BGRA,
        ]
        guard session.canAddOutput(videoOutput) else {
            throw ZCameraError.cannotAddOutput
        }
        session.addOutput(videoOutput)
        if let connection = videoOutput.connection(with: .video) {
            if connection.isVideoOrientationSupported {
                connection.videoOrientation = .portrait
            }
            if connection.isVideoMirroringSupported {
                connection.isVideoMirrored = device.position == .front
            }
        }

        depthOutput.isFilteringEnabled = true
        depthOutput.alwaysDiscardsLateDepthData = true
        guard session.canAddOutput(depthOutput) else {
            throw ZCameraError.cannotAddOutput
        }
        session.addOutput(depthOutput)
        if let depthConnection = depthOutput.connection(with: .depthData) {
            if depthConnection.isVideoOrientationSupported {
                depthConnection.videoOrientation = .portrait
            }
            if depthConnection.isVideoMirroringSupported {
                depthConnection.isVideoMirrored = device.position == .front
            }
        }

        try Self.selectDepthFormat(for: device)

        let synchronizer = AVCaptureDataOutputSynchronizer(dataOutputs: [videoOutput, depthOutput])
        synchronizer.setDelegate(self, queue: outputQueue)
        self.synchronizer = synchronizer

        bandLock.lock()
        bandForProcessing = initialBand
        overlayForProcessing = initialOverlay
        bandLock.unlock()

        return device
    }

    private static func preferredDepthDevice() -> AVCaptureDevice? {
        let discovery = AVCaptureDevice.DiscoverySession(
            deviceTypes: [
                .builtInLiDARDepthCamera,
                .builtInDualCamera,
                .builtInDualWideCamera,
                .builtInTrueDepthCamera,
            ],
            mediaType: .video,
            position: .unspecified
        )
        if let rear = discovery.devices.first(where: { $0.position == .back }) {
            return rear
        }
        return discovery.devices.first
    }

    private static func selectBestCaptureFormat(for device: AVCaptureDevice) throws {
        let pixelCap = 1280 * 720

        var bestFormat: AVCaptureDevice.Format?
        var bestScore = 0

        for format in device.formats {
            let dims = CMVideoFormatDescriptionGetDimensions(format.formatDescription)
            let pixels = Int(dims.width) * Int(dims.height)
            guard !format.supportedDepthDataFormats.isEmpty else { continue }
            guard pixels <= pixelCap * 2 else { continue }

            let bestDepthPixels = format.supportedDepthDataFormats.map {
                let depthDims = CMVideoFormatDescriptionGetDimensions($0.formatDescription)
                return Int(depthDims.width) * Int(depthDims.height)
            }.max() ?? 0

            // Prefer usable video resolution with the highest companion depth raster.
            let score = min(pixels, pixelCap) + bestDepthPixels * 3
            if score > bestScore {
                bestScore = score
                bestFormat = format
            }
        }

        guard let format = bestFormat else {
            throw ZCameraError.noDepthFormat
        }

        try device.lockForConfiguration()
        device.activeFormat = format
        device.unlockForConfiguration()
    }

    private static func selectDepthFormat(for device: AVCaptureDevice) throws {
        func depthPixels(_ format: AVCaptureDevice.Format) -> Int {
            let dims = CMVideoFormatDescriptionGetDimensions(format.formatDescription)
            return Int(dims.width) * Int(dims.height)
        }

        func chooseDepthFormat(from formats: [AVCaptureDevice.Format]) -> AVCaptureDevice.Format? {
            formats.max { lhs, rhs in
                let lPixels = depthPixels(lhs)
                let rPixels = depthPixels(rhs)
                if lPixels != rPixels { return lPixels < rPixels }
                let lIsFloat32 = CMFormatDescriptionGetMediaSubType(lhs.formatDescription) == kCVPixelFormatType_DepthFloat32
                let rIsFloat32 = CMFormatDescriptionGetMediaSubType(rhs.formatDescription) == kCVPixelFormatType_DepthFloat32
                if lIsFloat32 != rIsFloat32 { return !lIsFloat32 }
                return false
            }
        }

        var depthFormats = device.activeFormat.supportedDepthDataFormats
        if depthFormats.isEmpty,
           let formatWithDepth = device.formats.reversed().first(where: { !$0.supportedDepthDataFormats.isEmpty }) {
            try device.lockForConfiguration()
            device.activeFormat = formatWithDepth
            device.unlockForConfiguration()
            depthFormats = formatWithDepth.supportedDepthDataFormats
        }

        guard let depthFormat = chooseDepthFormat(from: depthFormats) else {
            throw ZCameraError.noDepthFormat
        }

        try device.lockForConfiguration()
        device.activeDepthDataFormat = depthFormat
        device.unlockForConfiguration()
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

    private func currentProcessingOptions() -> (band: ZDepthBand, overlay: Bool) {
        bandLock.lock()
        defer { bandLock.unlock() }
        return (bandForProcessing, overlayForProcessing)
    }

    private static func renderMaskedFrame(
        pixelBuffer: CVPixelBuffer,
        depthData: AVDepthData,
        band: ZDepthBand,
        overlayDepth: Bool
    ) -> UIImage? {
        let converted: AVDepthData
        if depthData.depthDataType != kCVPixelFormatType_DepthFloat32 {
            converted = depthData.converting(toDepthDataType: kCVPixelFormatType_DepthFloat32)
        } else {
            converted = depthData
        }
        let depthBuffer = converted.depthDataMap

        CVPixelBufferLockBaseAddress(pixelBuffer, .readOnly)
        CVPixelBufferLockBaseAddress(depthBuffer, .readOnly)
        defer {
            CVPixelBufferUnlockBaseAddress(depthBuffer, .readOnly)
            CVPixelBufferUnlockBaseAddress(pixelBuffer, .readOnly)
        }

        let width = CVPixelBufferGetWidth(pixelBuffer)
        let height = CVPixelBufferGetHeight(pixelBuffer)
        let bytesPerRow = CVPixelBufferGetBytesPerRow(pixelBuffer)
        let depthWidth = CVPixelBufferGetWidth(depthBuffer)
        let depthHeight = CVPixelBufferGetHeight(depthBuffer)
        let depthBytesPerRow = CVPixelBufferGetBytesPerRow(depthBuffer)

        guard
            let base = CVPixelBufferGetBaseAddress(pixelBuffer)?.assumingMemoryBound(to: UInt8.self),
            let depthBase = CVPixelBufferGetBaseAddress(depthBuffer)?.assumingMemoryBound(to: Float.self)
        else {
            return nil
        }

        let mapper = ZDepthCoordinateMapper(
            videoWidth: width,
            videoHeight: height,
            depthWidth: depthWidth,
            depthHeight: depthHeight,
            calibration: converted.cameraCalibrationData
        )

        let dataSize = bytesPerRow * height
        let copy = UnsafeMutablePointer<UInt8>.allocate(capacity: dataSize)
        defer { copy.deallocate() }
        copy.initialize(from: base, count: dataSize)

        // Mirroring is applied on the capture connections for the front camera.
        ZDepthBandMasker.applyBandInPlace(
            bgra: copy,
            width: width,
            height: height,
            bytesPerRow: bytesPerRow,
            depth: depthBase,
            depthWidth: depthWidth,
            depthHeight: depthHeight,
            depthBytesPerRow: depthBytesPerRow,
            band: band,
            mapper: mapper,
            mirrorX: false,
            overlayDepth: overlayDepth
        )

        guard let context = CGContext(
            data: copy,
            width: width,
            height: height,
            bitsPerComponent: 8,
            bytesPerRow: bytesPerRow,
            space: CGColorSpaceCreateDeviceRGB(),
            bitmapInfo: CGImageAlphaInfo.premultipliedFirst.rawValue
                | CGBitmapInfo.byteOrder32Little.rawValue
        ), let cgImage = context.makeImage() else {
            return nil
        }
        return UIImage(cgImage: cgImage, scale: 1, orientation: .up)
    }
}

enum ZCameraError: Error, Equatable, LocalizedError {
    case noDepthCamera
    case noDepthFormat
    case cannotAddInput
    case cannotAddOutput

    var errorDescription: String? {
        switch self {
        case .noDepthCamera:
            return "No depth-capable camera is available."
        case .noDepthFormat:
            return "Camera has no usable depth format."
        case .cannotAddInput:
            return "Couldn't add the camera input."
        case .cannotAddOutput:
            return "Couldn't add camera outputs."
        }
    }
}

extension ZCameraSession: AVCaptureDataOutputSynchronizerDelegate {
    func dataOutputSynchronizer(
        _ synchronizer: AVCaptureDataOutputSynchronizer,
        didOutput synchronizedDataCollection: AVCaptureSynchronizedDataCollection
    ) {
        guard
            let videoData = synchronizedDataCollection.synchronizedData(for: videoOutput)
                as? AVCaptureSynchronizedSampleBufferData,
            !videoData.sampleBufferWasDropped,
            let depthData = synchronizedDataCollection.synchronizedData(for: depthOutput)
                as? AVCaptureSynchronizedDepthData,
            !depthData.depthDataWasDropped,
            let pixelBuffer = CMSampleBufferGetImageBuffer(videoData.sampleBuffer)
        else {
            return
        }

        let options = currentProcessingOptions()
        guard let image = Self.renderMaskedFrame(
            pixelBuffer: pixelBuffer,
            depthData: depthData.depthData,
            band: options.band,
            overlayDepth: options.overlay
        ) else {
            return
        }

        DispatchQueue.main.async { [weak self] in
            self?.previewImage = image
        }
    }
}
