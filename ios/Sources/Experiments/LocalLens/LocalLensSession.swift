import AVFoundation
import CoreImage
import QuartzCore
import UIKit

/// Live camera session that runs on-device Vision analysis and publishes preview + findings.
final class LocalLensSession: NSObject, ObservableObject {
    enum RunState: Equatable {
        case idle
        case requestingPermission
        case running
        case noCamera
        case permissionDenied
        case failed(String)
    }

    @Published private(set) var runState: RunState = .idle
    @Published private(set) var statusMessage = "Everything stays on this device — no network."
    @Published private(set) var previewImage: UIImage?
    /// Pixel size of the upright preview / Vision image (matches published `previewImage`).
    @Published private(set) var previewImageSize: CGSize = .zero
    @Published private(set) var result = LocalLensFrameResult.empty(mode: .classify)
    @Published private(set) var mode: LocalLensMode = .classify
    @Published private(set) var usingFrontCamera = false

    private let session = AVCaptureSession()
    private let videoOutput = AVCaptureVideoDataOutput()
    private let sessionQueue = DispatchQueue(label: "local-lens.session")
    private let outputQueue = DispatchQueue(label: "local-lens.output", qos: .userInitiated)
    private let analyzer = LocalLensAnalyzer()
    private let previewContext = CIContext(options: [.useSoftwareRenderer: false])

    private let stateLock = NSLock()
    private var modeForProcessing: LocalLensMode = .classify
    private var cameraPosition: AVCaptureDevice.Position = .back
    private var deviceOrientation: UIDeviceOrientation = .portrait
    private var lastAnalyzeTime: CFTimeInterval = 0
    private let analyzeInterval: CFTimeInterval = 0.22
    private var isAnalyzing = false
    private var orientationObserver: NSObjectProtocol?

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
        DispatchQueue.main.async { [weak self] in
            guard let self else { return }
            self.previewImage = nil
            self.previewImageSize = .zero
            if self.runState == .running {
                self.runState = .idle
                self.statusMessage = "Stopped. Frames never left this device."
            }
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
            let changed = self.deviceOrientation != next
            self.deviceOrientation = next
            self.stateLock.unlock()
            guard changed else { return }
            self.sessionQueue.async {
                self.applyCaptureOrientation(next)
            }
            // Drop stale boxes until the next upright frame arrives.
            self.result = .empty(mode: self.mode)
        }
    }

    private func endOrientationUpdates() {
        if let orientationObserver {
            NotificationCenter.default.removeObserver(orientationObserver)
            self.orientationObserver = nil
        }
        UIDevice.current.endGeneratingDeviceOrientationNotifications()
    }

    func setMode(_ mode: LocalLensMode) {
        self.mode = mode
        stateLock.lock()
        modeForProcessing = mode
        stateLock.unlock()
        result = .empty(mode: mode)
        if runState == .running {
            statusMessage = mode.blurb
        }
    }

    func flipCamera() {
        sessionQueue.async { [weak self] in
            guard let self else { return }
            let next: AVCaptureDevice.Position = self.cameraPosition == .back ? .front : .back
            do {
                try self.reconfigure(for: next)
                DispatchQueue.main.async {
                    self.usingFrontCamera = next == .front
                    self.result = .empty(mode: self.mode)
                    self.statusMessage = next == .front
                        ? "Front camera — \(self.mode.blurb)"
                        : "Rear camera — \(self.mode.blurb)"
                }
            } catch {
                DispatchQueue.main.async {
                    self.statusMessage = error.localizedDescription
                }
            }
        }
    }

    // MARK: - Configuration

    private func configureAndStart() {
        sessionQueue.async { [weak self] in
            guard let self else { return }
            do {
                try self.configureSession(position: .back)
                self.session.startRunning()
                DispatchQueue.main.async {
                    self.usingFrontCamera = false
                    self.runState = .running
                    self.statusMessage = self.mode.blurb
                }
            } catch let error as LocalLensError where error == .noCamera {
                DispatchQueue.main.async {
                    self.runState = .noCamera
                    self.statusMessage = "No camera on this device (Simulator has none). Try a physical iPhone."
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

        session.sessionPreset = .high

        for input in session.inputs {
            session.removeInput(input)
        }
        for output in session.outputs {
            session.removeOutput(output)
        }

        guard let device = Self.camera(for: position) else {
            throw LocalLensError.noCamera
        }
        let input = try AVCaptureDeviceInput(device: device)
        guard session.canAddInput(input) else {
            throw LocalLensError.cannotAddInput
        }
        session.addInput(input)

        videoOutput.alwaysDiscardsLateVideoFrames = true
        videoOutput.videoSettings = [
            kCVPixelBufferPixelFormatTypeKey as String: kCVPixelFormatType_32BGRA
        ]
        guard session.canAddOutput(videoOutput) else {
            throw LocalLensError.cannotAddOutput
        }
        session.addOutput(videoOutput)
        videoOutput.setSampleBufferDelegate(self, queue: outputQueue)

        cameraPosition = position
        stateLock.lock()
        let orientation = deviceOrientation
        stateLock.unlock()
        applyCaptureOrientation(orientation, position: position)
    }

    private func reconfigure(for position: AVCaptureDevice.Position) throws {
        try configureSession(position: position)
    }

    private func applyCaptureOrientation(
        _ deviceOrientation: UIDeviceOrientation,
        position: AVCaptureDevice.Position? = nil
    ) {
        guard let connection = videoOutput.connection(with: .video) else { return }
        let cam = position ?? cameraPosition
        if connection.isVideoOrientationSupported {
            connection.videoOrientation = LocalLensCoordinateMapper.captureOrientation(
                for: deviceOrientation
            )
        }
        if connection.isVideoMirroringSupported {
            connection.isVideoMirrored = cam == .front
            // Prefer mirroring after orientation so front preview matches what Vision sees.
            if connection.isVideoOrientationSupported {
                connection.videoOrientation = LocalLensCoordinateMapper.captureOrientation(
                    for: deviceOrientation
                )
            }
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

    private static func resolvedDeviceOrientation(_ raw: UIDeviceOrientation) -> UIDeviceOrientation {
        switch raw {
        case .portrait, .portraitUpsideDown, .landscapeLeft, .landscapeRight:
            return raw
        default:
            // Flat / unknown — keep the interface orientation if we can.
            if let scene = UIApplication.shared.connectedScenes
                .compactMap({ $0 as? UIWindowScene })
                .first
            {
                switch scene.interfaceOrientation {
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

    private func currentMode() -> LocalLensMode {
        stateLock.lock()
        defer { stateLock.unlock() }
        return modeForProcessing
    }
}

enum LocalLensError: Error, Equatable, LocalizedError {
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

extension LocalLensSession: AVCaptureVideoDataOutputSampleBufferDelegate {
    func captureOutput(
        _ output: AVCaptureOutput,
        didOutput sampleBuffer: CMSampleBuffer,
        from connection: AVCaptureConnection
    ) {
        guard let pixelBuffer = CMSampleBufferGetImageBuffer(sampleBuffer) else { return }

        let width = CVPixelBufferGetWidth(pixelBuffer)
        let height = CVPixelBufferGetHeight(pixelBuffer)
        let imageSize = CGSize(width: width, height: height)

        let ciImage = CIImage(cvPixelBuffer: pixelBuffer)
        if let cgImage = previewContext.createCGImage(ciImage, from: ciImage.extent) {
            let image = UIImage(cgImage: cgImage)
            DispatchQueue.main.async { [weak self] in
                self?.previewImage = image
                self?.previewImageSize = imageSize
            }
        }

        let now = CACurrentMediaTime()
        stateLock.lock()
        let shouldAnalyze = !isAnalyzing && (now - lastAnalyzeTime) >= analyzeInterval
        if shouldAnalyze {
            isAnalyzing = true
            lastAnalyzeTime = now
        }
        stateLock.unlock()

        guard shouldAnalyze else { return }

        let mode = currentMode()
        // Buffer is already upright via `connection.videoOrientation`, so Vision uses `.up`.
        // Front mirroring is applied on the connection, matching the published preview.
        do {
            let frameResult = try analyzer.analyze(
                pixelBuffer: pixelBuffer,
                mode: mode,
                orientation: .up
            )
            DispatchQueue.main.async { [weak self] in
                guard let self else { return }
                guard self.mode == mode else { return }
                self.result = frameResult
                if frameResult.findings.isEmpty {
                    self.statusMessage = LocalLensResultBuilder.emptyStatus(for: mode)
                } else {
                    let boxed = frameResult.findings.filter { $0.boundingBox != nil }.count
                    if boxed > 0 {
                        self.statusMessage = "\(boxed) in view · \(mode.title)"
                    } else {
                        let top = frameResult.findings.prefix(3)
                            .map { LocalLensResultBuilder.chipText(for: $0) }
                            .joined(separator: " · ")
                        self.statusMessage = top
                    }
                }
            }
        } catch {
            DispatchQueue.main.async { [weak self] in
                self?.statusMessage = "Vision error: \(error.localizedDescription)"
            }
        }

        stateLock.lock()
        isAnalyzing = false
        stateLock.unlock()
    }
}
