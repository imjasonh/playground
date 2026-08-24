import ARKit
import AVFoundation
import CoreImage
import UIKit
import Vision

final class DoomFaceSession: NSObject, ObservableObject {
    enum RunState: Equatable {
        case idle
        case unsupported
        case requestingPermission
        case permissionDenied
        case running
        case failed(String)
    }

    @Published private(set) var runState: RunState = .idle
    @Published private(set) var statusMessage = "Hold a doom face to stamp it on the sheet."
    @Published private(set) var previewImage: UIImage?
    @Published private(set) var liveExpression: DoomFaceExpression?
    @Published private(set) var holdProgress: Double = 0
    @Published private(set) var captures: [DoomFaceSlot: UIImage] = [:]
    @Published private(set) var sheetImage: UIImage?

    private let session = ARSession()
    private let sessionQueue = DispatchQueue(label: "doom-face.session")
    private let ciContext = CIContext(options: [.useSoftwareRenderer: false])
    private var holdTracker = DoomFaceMatcher.HoldTracker()
    private var greyTemplate: UIImage?
    private var lastPreviewTime: TimeInterval = 0

    override init() {
        super.init()
        session.delegate = self
        if let template = DoomFaceCompositor.loadTemplate() {
            greyTemplate = DoomFaceCompositor.greyscaleTemplate(from: template) ?? template
            sheetImage = greyTemplate
        }
    }

    var filledCount: Int { captures.count }
    var totalSlots: Int { DoomFaceSheetLayout.allSlots.count }
    var canExportGIF: Bool { DoomFaceGIFExporter.frames(from: captures).count >= 2 }

    func start() {
        switch runState {
        case .running, .requestingPermission:
            return
        default:
            break
        }

        guard ARFaceTrackingConfiguration.isSupported else {
            runState = .unsupported
            statusMessage = "Needs a TrueDepth front camera. Simulator can't track a face."
            return
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
            self.runSession()
        }
    }

    func stop() {
        session.pause()
        if runState == .running {
            runState = .idle
            statusMessage = "Stopped."
        }
        previewImage = nil
        liveExpression = nil
        holdProgress = 0
    }

    func resetCaptures() {
        captures = [:]
        holdTracker.reset()
        sheetImage = greyTemplate
        statusMessage = "Sheet cleared."
    }

    func exportGIFURL() throws -> URL {
        try DoomFaceGIFExporter.writeTemporaryGIF(captures: captures)
    }

    private func runSession() {
        let configuration = ARFaceTrackingConfiguration()
        configuration.maximumNumberOfTrackedFaces = 1
        session.run(configuration, options: [.resetTracking, .removeExistingAnchors])
        runState = .running
        statusMessage = "Look left, grin, or open wide. Hold it."
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

    private func handle(frame: ARFrame) {
        let now = frame.timestamp
        if now - lastPreviewTime >= 0.05 {
            lastPreviewTime = now
            if let preview = makePreview(from: frame.capturedImage) {
                DispatchQueue.main.async { self.previewImage = preview }
            }
        }

        guard let faceAnchor = frame.anchors.compactMap({ $0 as? ARFaceAnchor }).first,
              faceAnchor.isTracked
        else {
            holdTracker.reset()
            DispatchQueue.main.async {
                self.liveExpression = nil
                self.holdProgress = 0
            }
            return
        }

        let expression = DoomFaceMatcher.match(Self.blendSample(from: faceAnchor))
        let progress = holdTracker.progress(for: expression)
        let held = holdTracker.update(expression)

        DispatchQueue.main.async {
            self.liveExpression = expression
            self.holdProgress = held != nil ? 1 : progress
        }

        if let held {
            captureFace(for: held, pixelBuffer: frame.capturedImage)
        }
    }

    private func captureFace(for expression: DoomFaceExpression, pixelBuffer: CVPixelBuffer) {
        let filled = Set(captures.keys)
        guard let slot = DoomFaceSheetLayout.nextEmptySlot(for: expression, filled: filled) else {
            DispatchQueue.main.async {
                self.statusMessage = "\(expression.displayName) is already full."
            }
            return
        }

        guard let cropped = cropFace(from: pixelBuffer) else {
            DispatchQueue.main.async {
                self.statusMessage = "Couldn't crop that face. Try again."
            }
            return
        }

        let fitted = DoomFaceCompositor.fitFace(cropped)
        DispatchQueue.main.async {
            self.captures[slot] = fitted
            self.rebuildSheet()
            if let health = slot.health {
                self.statusMessage = "\(expression.displayName), health row \(health + 1)."
            } else {
                self.statusMessage = "\(expression.displayName)."
            }
        }
    }

    private func rebuildSheet() {
        guard let grey = greyTemplate else { return }
        sheetImage = DoomFaceCompositor.compose(greyscaleTemplate: grey, captures: captures)
    }

    private func makePreview(from pixelBuffer: CVPixelBuffer) -> UIImage? {
        let image = CIImage(cvPixelBuffer: pixelBuffer).oriented(.leftMirrored)
        guard let cgImage = ciContext.createCGImage(image, from: image.extent) else { return nil }
        return UIImage(cgImage: cgImage)
    }

    private static func blendSample(from anchor: ARFaceAnchor) -> DoomFaceBlendSample {
        let b = anchor.blendShapes
        func value(_ key: ARFaceAnchor.BlendShapeLocation) -> Double {
            Double(b[key]?.floatValue ?? 0)
        }

        return DoomFaceBlendSample(
            lookLeft: (value(.eyeLookOutLeft) + value(.eyeLookInRight)) / 2,
            lookRight: (value(.eyeLookOutRight) + value(.eyeLookInLeft)) / 2,
            lookUp: (value(.eyeLookUpLeft) + value(.eyeLookUpRight)) / 2,
            lookDown: (value(.eyeLookDownLeft) + value(.eyeLookDownRight)) / 2,
            jawOpen: value(.jawOpen),
            smile: max(value(.mouthSmileLeft), value(.mouthSmileRight)),
            browDown: max(value(.browDownLeft), value(.browDownRight)),
            eyeWide: max(value(.eyeWideLeft), value(.eyeWideRight)),
            eyeBlink: min(value(.eyeBlinkLeft), value(.eyeBlinkRight))
        )
    }

    private func cropFace(from pixelBuffer: CVPixelBuffer) -> UIImage? {
        var image = CIImage(cvPixelBuffer: pixelBuffer).oriented(.leftMirrored)
        let extent = image.extent
        guard extent.width > 0, extent.height > 0 else { return nil }

        let handler = VNImageRequestHandler(ciImage: image, options: [:])
        let request = VNDetectFaceRectanglesRequest()
        try? handler.perform([request])

        let faceBox: CGRect
        if let box = request.results?.first?.boundingBox {
            let padded = box.insetBy(dx: -box.width * 0.12, dy: -box.height * 0.18)
                .intersection(CGRect(x: 0, y: 0, width: 1, height: 1))
            faceBox = CGRect(
                x: extent.minX + padded.minX * extent.width,
                y: extent.minY + padded.minY * extent.height,
                width: padded.width * extent.width,
                height: padded.height * extent.height
            ).integral
        } else {
            let side = min(extent.width, extent.height) * 0.55
            faceBox = CGRect(
                x: extent.midX - side / 2,
                y: extent.midY - side / 2,
                width: side,
                height: side
            ).integral
        }

        image = image.cropped(to: faceBox)
        image = image.transformed(by: CGAffineTransform(
            translationX: -image.extent.origin.x,
            y: -image.extent.origin.y
        ))
        guard let cgImage = ciContext.createCGImage(image, from: image.extent) else { return nil }
        return UIImage(cgImage: cgImage)
    }
}

extension DoomFaceSession: ARSessionDelegate {
    func session(_ session: ARSession, didUpdate frame: ARFrame) {
        sessionQueue.async { [weak self] in
            self?.handle(frame: frame)
        }
    }

    func session(_ session: ARSession, didFailWithError error: Error) {
        DispatchQueue.main.async {
            self.runState = .failed(error.localizedDescription)
            self.statusMessage = error.localizedDescription
        }
    }
}
