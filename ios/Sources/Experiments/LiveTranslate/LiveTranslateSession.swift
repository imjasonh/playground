import AVFoundation
import CoreImage
import FoundationModels
import QuartzCore
import UIKit

/// Live camera session that OCRs frames, translates stable text, and copies the result.
final class LiveTranslateSession: NSObject, ObservableObject {
    enum RunState: Equatable {
        case idle
        case requestingPermission
        case running
        case noCamera
        case permissionDenied
        case failed(String)
    }

    @Published private(set) var runState: RunState = .idle
    @Published private(set) var statusMessage = "Point the camera at text."
    @Published private(set) var previewImage: UIImage?
    @Published private(set) var previewImageSize: CGSize = .zero
    @Published private(set) var overlays: [LiveTranslateOverlay] = []
    @Published private(set) var language: LiveTranslateLanguage = .english
    @Published private(set) var usingFrontCamera = false
    @Published private(set) var modelGate: AgentModelGate
    @Published private(set) var isTranslating = false
    @Published private(set) var didCopy = false

    private let session = AVCaptureSession()
    private let videoOutput = AVCaptureVideoDataOutput()
    private let sessionQueue = DispatchQueue(label: "live-translate.session")
    private let outputQueue = DispatchQueue(label: "live-translate.output", qos: .userInitiated)
    private let previewContext = CIContext(options: [.useSoftwareRenderer: false])

    private let stateLock = NSLock()
    private var cameraPosition: AVCaptureDevice.Position = .back
    private var deviceOrientation: UIDeviceOrientation = .portrait
    private var languageForProcessing: LiveTranslateLanguage = .english
    private var lastAnalyzeTime: CFTimeInterval = 0
    private let analyzeInterval: CFTimeInterval = 0.22
    private var isAnalyzing = false
    private var orientationObserver: NSObjectProtocol?

    private var lastObservations: [LiveTranslateObservation] = []
    private var lastItems: [LiveTranslateItem] = []
    private var lastTranslatedFingerprint = ""
    private var pendingFingerprint: String?
    private var pendingSince: Date?
    private var lastCopiedPayload: String?
    private var translateGeneration = 0
    private var translateTask: Task<Void, Never>?

    override init() {
        modelGate = Self.readGate()
        super.init()
    }

    var canCopy: Bool {
        !LiveTranslateResultBuilder.clipboardPayload(from: overlays).isEmpty
    }

    func start() {
        switch runState {
        case .running, .requestingPermission:
            return
        default:
            break
        }

        refreshModelStatus()
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
        translateTask?.cancel()
        translateTask = nil
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
            self.overlays = []
            if self.runState == .running {
                self.runState = .idle
                self.statusMessage = "Stopped."
            }
        }
    }

    func refreshModelStatus() {
        modelGate = Self.readGate()
    }

    func setLanguage(_ language: LiveTranslateLanguage) {
        self.language = language
        stateLock.lock()
        languageForProcessing = language
        stateLock.unlock()
        lastTranslatedFingerprint = ""
        lastItems = []
        pendingFingerprint = nil
        pendingSince = nil
        didCopy = false
        if runState == .running {
            statusMessage = "Translate to \(language.displayName)."
            publishOverlays(observations: lastObservations, items: [], image: nil)
            if !lastObservations.isEmpty {
                requestTranslation(observations: lastObservations, language: language)
            }
        }
    }

    func copyToClipboard() {
        let payload = LiveTranslateResultBuilder.clipboardPayload(from: overlays)
        guard !payload.isEmpty else { return }
        writeClipboard(payload)
    }

    func flipCamera() {
        sessionQueue.async { [weak self] in
            guard let self else { return }
            let next: AVCaptureDevice.Position = self.cameraPosition == .back ? .front : .back
            do {
                try self.reconfigure(for: next)
                DispatchQueue.main.async {
                    self.usingFrontCamera = next == .front
                    self.lastObservations = []
                    self.lastItems = []
                    self.lastTranslatedFingerprint = ""
                    self.pendingFingerprint = nil
                    self.overlays = []
                    self.statusMessage = next == .front
                        ? "Front camera. Point at text."
                        : "Rear camera. Point at text."
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
                    self.statusMessage = self.modelGate.isAvailable
                        ? "Point at printed or on-screen text."
                        : self.modelUnavailableStatus()
                }
            } catch let error as LiveTranslateError where error == .noCamera {
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
            throw LiveTranslateError.noCamera
        }
        let input = try AVCaptureDeviceInput(device: device)
        guard session.canAddInput(input) else {
            throw LiveTranslateError.cannotAddInput
        }
        session.addInput(input)

        videoOutput.alwaysDiscardsLateVideoFrames = true
        videoOutput.videoSettings = [
            kCVPixelBufferPixelFormatTypeKey as String: kCVPixelFormatType_32BGRA
        ]
        guard session.canAddOutput(videoOutput) else {
            throw LiveTranslateError.cannotAddOutput
        }
        session.addOutput(videoOutput)
        videoOutput.setSampleBufferDelegate(self, queue: outputQueue)

        cameraPosition = position
        disableBufferMirroring()
    }

    private func reconfigure(for position: AVCaptureDevice.Position) throws {
        try configureSession(position: position)
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
            let changed = self.deviceOrientation != next
            self.deviceOrientation = next
            self.stateLock.unlock()
            guard changed else { return }
            self.overlays = []
            self.lastObservations = []
            self.lastTranslatedFingerprint = ""
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

    private func currentLanguage() -> LiveTranslateLanguage {
        stateLock.lock()
        defer { stateLock.unlock() }
        return languageForProcessing
    }

    private static func readGate() -> AgentModelGate {
        switch SystemLanguageModel.default.availability {
        case .available:
            return .available
        case .unavailable(.deviceNotEligible):
            return .deviceNotEligible
        case .unavailable(.appleIntelligenceNotEnabled):
            return .needsAppleIntelligence
        case .unavailable(.modelNotReady):
            return .modelNotReady
        case .unavailable(let reason):
            return .other("Apple Intelligence isn't available (\(String(describing: reason))).")
        @unknown default:
            return .other("Apple Intelligence isn't available on this device.")
        }
    }

    private func modelUnavailableStatus() -> String {
        switch modelGate {
        case .needsAppleIntelligence:
            return "Turn on Apple Intelligence to translate."
        case .modelNotReady:
            return "The on-device model is still downloading."
        case .deviceNotEligible:
            return "This iPhone doesn't support Apple Intelligence."
        case .other(let reason):
            return reason
        case .available:
            return "Point at printed or on-screen text."
        }
    }

    // MARK: - Overlay + clipboard

    private func publishOverlays(
        observations: [LiveTranslateObservation],
        items: [LiveTranslateItem],
        image: CGImage?
    ) {
        let sampleImage = image ?? previewImage?.cgImage
        var backdrops: [String: LiveTranslateBackdrop] = [:]
        if let sampleImage {
            for observation in observations {
                backdrops[observation.id] = LiveTranslateColor.sample(
                    image: sampleImage,
                    visionBox: observation.boundingBox
                )
            }
        }
        overlays = LiveTranslateResultBuilder.overlays(
            observations: observations,
            items: items,
            backdrops: backdrops
        )
        maybeCopy(overlays)
    }

    private func maybeCopy(_ overlays: [LiveTranslateOverlay]) {
        let payload = LiveTranslateResultBuilder.clipboardPayload(from: overlays)
        guard LiveTranslateResultBuilder.shouldCopy(newPayload: payload, lastCopied: lastCopiedPayload) else {
            return
        }
        guard overlays.contains(where: \.isTranslated) || !modelGate.isAvailable else {
            return
        }
        writeClipboard(payload)
    }

    private func writeClipboard(_ payload: String) {
        UIPasteboard.general.string = payload
        lastCopiedPayload = payload
        didCopy = true
        statusMessage = "Copied"
        UINotificationFeedbackGenerator().notificationOccurred(.success)
        DispatchQueue.main.asyncAfter(deadline: .now() + 2) { [weak self] in
            guard let self, self.lastCopiedPayload == payload else { return }
            self.didCopy = false
            if self.statusMessage == "Copied" {
                self.statusMessage = self.countStatus()
            }
        }
    }

    private func countStatus() -> String {
        let translated = overlays.filter(\.isTranslated).count
        if translated == 0 {
            return modelGate.isAvailable
                ? "Point at printed or on-screen text."
                : modelUnavailableStatus()
        }
        if translated == 1 {
            return "1 line · \(language.displayName)"
        }
        return "\(translated) lines · \(language.displayName)"
    }

    private func requestTranslation(
        observations: [LiveTranslateObservation],
        language: LiveTranslateLanguage
    ) {
        guard modelGate.isAvailable else { return }
        translateGeneration += 1
        let generation = translateGeneration
        translateTask?.cancel()
        isTranslating = true
        if !didCopy {
            statusMessage = "Translating…"
        }
        translateTask = Task { [weak self] in
            do {
                let items = try await LiveTranslateTranslator.translate(
                    observations: observations,
                    language: language
                )
                DispatchQueue.main.async { [weak self] in
                    guard let self, generation == self.translateGeneration else { return }
                    self.isTranslating = false
                    self.lastItems = items
                    self.lastTranslatedFingerprint = LiveTranslateResultBuilder.fingerprint(for: observations)
                    self.publishOverlays(observations: self.lastObservations, items: items, image: nil)
                    if !self.didCopy {
                        self.statusMessage = self.countStatus()
                    }
                }
            } catch {
                let message = error.localizedDescription
                DispatchQueue.main.async { [weak self] in
                    guard let self, generation == self.translateGeneration else { return }
                    self.isTranslating = false
                    self.statusMessage = message
                }
            }
        }
    }
}

enum LiveTranslateError: Error, Equatable, LocalizedError {
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

extension LiveTranslateSession: AVCaptureVideoDataOutputSampleBufferDelegate {
    func captureOutput(
        _ output: AVCaptureOutput,
        didOutput sampleBuffer: CMSampleBuffer,
        from connection: AVCaptureConnection
    ) {
        guard let pixelBuffer = CMSampleBufferGetImageBuffer(sampleBuffer) else { return }

        let (deviceOrientation, position) = currentOrientationAndCamera()
        let orientation = LocalLensCoordinateMapper.visionOrientation(
            deviceOrientation: deviceOrientation,
            cameraPosition: position
        )

        let upright = LocalLensCoordinateMapper.uprightCIImage(
            from: pixelBuffer,
            orientation: orientation
        )
        let uprightSize = upright.extent.size
        let previewCGImage = previewContext.createCGImage(upright, from: upright.extent)
        if let previewCGImage {
            let image = UIImage(cgImage: previewCGImage)
            DispatchQueue.main.async { [weak self] in
                self?.previewImage = image
                self?.previewImageSize = uprightSize
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

        let language = currentLanguage()
        do {
            let observations = try LiveTranslateRecognizer.recognize(
                pixelBuffer: pixelBuffer,
                orientation: orientation
            )
            let fingerprint = LiveTranslateResultBuilder.fingerprint(for: observations)
            DispatchQueue.main.async { [weak self] in
                guard let self else { return }
                self.handleOCR(
                    observations: observations,
                    fingerprint: fingerprint,
                    language: language,
                    image: previewCGImage
                )
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

    private func handleOCR(
        observations: [LiveTranslateObservation],
        fingerprint: String,
        language: LiveTranslateLanguage,
        image: CGImage?
    ) {
        lastObservations = observations
        let items = fingerprint == lastTranslatedFingerprint ? lastItems : []
        publishOverlays(observations: observations, items: items, image: image)

        if observations.isEmpty {
            pendingFingerprint = nil
            pendingSince = nil
            if !isTranslating && !didCopy {
                statusMessage = modelGate.isAvailable
                    ? "Point at printed or on-screen text."
                    : modelUnavailableStatus()
            }
            return
        }

        if fingerprint == lastTranslatedFingerprint {
            return
        }

        if !modelGate.isAvailable {
            if !didCopy {
                statusMessage = modelUnavailableStatus()
            }
            return
        }

        let now = Date()
        if fingerprint != pendingFingerprint {
            pendingFingerprint = fingerprint
            pendingSince = now
            return
        }

        guard !isTranslating else { return }
        guard LiveTranslateResultBuilder.shouldTranslate(
            current: fingerprint,
            pending: pendingFingerprint,
            pendingSince: pendingSince,
            now: now
        ) else {
            return
        }
        requestTranslation(observations: observations, language: language)
    }
}
