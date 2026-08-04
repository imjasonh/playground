import AVFoundation
import CoreVideo
import Foundation
import UIKit
import Vision

/// Runs one on-device Vision request against a camera frame. No network.
final class LocalLensAnalyzer {
    func analyze(pixelBuffer: CVPixelBuffer, mode: LocalLensMode, orientation: CGImagePropertyOrientation) throws -> LocalLensFrameResult {
        let handler = VNImageRequestHandler(cvPixelBuffer: pixelBuffer, orientation: orientation, options: [:])
        switch mode {
        case .classify:
            return try classify(handler: handler)
        case .text:
            return try recognizeText(handler: handler)
        case .animals:
            return try recognizeAnimals(handler: handler)
        case .faces:
            return try detectFaces(handler: handler)
        case .people:
            return try detectPeople(handler: handler)
        case .barcodes:
            return try detectBarcodes(handler: handler)
        }
    }

    /// Test helper: analyze a CGImage the same way as a live frame.
    func analyze(cgImage: CGImage, mode: LocalLensMode, orientation: CGImagePropertyOrientation = .up) throws -> LocalLensFrameResult {
        let handler = VNImageRequestHandler(cgImage: cgImage, orientation: orientation, options: [:])
        switch mode {
        case .classify:
            return try classify(handler: handler)
        case .text:
            return try recognizeText(handler: handler)
        case .animals:
            return try recognizeAnimals(handler: handler)
        case .faces:
            return try detectFaces(handler: handler)
        case .people:
            return try detectPeople(handler: handler)
        case .barcodes:
            return try detectBarcodes(handler: handler)
        }
    }

    // MARK: - Requests

    private func classify(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNClassifyImageRequest()
        try handler.perform([request])
        let findings = (request.results ?? []).map { observation in
            LocalLensFinding(
                id: observation.identifier,
                label: Self.prettyLabel(observation.identifier),
                confidence: Double(observation.confidence)
            )
        }
        return LocalLensResultBuilder.build(mode: .classify, findings: findings)
    }

    private func recognizeText(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNRecognizeTextRequest()
        request.recognitionLevel = .accurate
        request.usesLanguageCorrection = true
        try handler.perform([request])
        let findings = (request.results ?? []).compactMap { observation -> LocalLensFinding? in
            guard let top = observation.topCandidates(1).first else { return nil }
            return LocalLensFinding(
                label: top.string,
                confidence: Double(top.confidence),
                boundingBox: observation.boundingBox
            )
        }
        // OCR confidences are often high; keep short snippets too.
        return LocalLensResultBuilder.build(
            mode: .text,
            findings: findings,
            minimumConfidence: 0.3,
            maxFindings: 8
        )
    }

    private func recognizeAnimals(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNRecognizeAnimalsRequest()
        try handler.perform([request])
        let findings = (request.results ?? []).flatMap { observation -> [LocalLensFinding] in
            observation.labels.map { label in
                LocalLensFinding(
                    label: Self.prettyLabel(label.identifier),
                    confidence: Double(label.confidence),
                    boundingBox: observation.boundingBox
                )
            }
        }
        return LocalLensResultBuilder.build(mode: .animals, findings: findings, minimumConfidence: 0.2)
    }

    private func detectFaces(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNDetectFaceRectanglesRequest()
        try handler.perform([request])
        let findings = (request.results ?? []).enumerated().map { index, observation in
            LocalLensFinding(
                label: "Face \(index + 1)",
                confidence: Double(observation.confidence),
                boundingBox: observation.boundingBox
            )
        }
        return LocalLensResultBuilder.build(mode: .faces, findings: findings, minimumConfidence: 0.2)
    }

    private func detectPeople(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNDetectHumanRectanglesRequest()
        try handler.perform([request])
        let findings = (request.results ?? []).enumerated().map { index, observation in
            LocalLensFinding(
                label: "Person \(index + 1)",
                confidence: Double(observation.confidence),
                boundingBox: observation.boundingBox
            )
        }
        return LocalLensResultBuilder.build(mode: .people, findings: findings, minimumConfidence: 0.2)
    }

    private func detectBarcodes(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNDetectBarcodesRequest()
        try handler.perform([request])
        let findings = (request.results ?? []).compactMap { observation -> LocalLensFinding? in
            let payload = observation.payloadStringValue?.trimmingCharacters(in: .whitespacesAndNewlines)
            let symbology = Self.prettySymbology(observation.symbology)
            let label: String
            if let payload, !payload.isEmpty {
                let clipped = payload.count > 40 ? String(payload.prefix(37)) + "…" : payload
                label = "\(symbology): \(clipped)"
            } else {
                label = symbology
            }
            return LocalLensFinding(
                label: label,
                confidence: Double(observation.confidence),
                boundingBox: observation.boundingBox
            )
        }
        return LocalLensResultBuilder.build(mode: .barcodes, findings: findings, minimumConfidence: 0.1)
    }

    // MARK: - Formatting

    static func prettyLabel(_ identifier: String) -> String {
        identifier
            .replacingOccurrences(of: "_", with: " ")
            .replacingOccurrences(of: "-", with: " ")
            .split(separator: " ")
            .map { part -> String in
                let lower = part.lowercased()
                guard let first = lower.first else { return String(part) }
                return String(first).uppercased() + lower.dropFirst()
            }
            .joined(separator: " ")
    }

    static func prettySymbology(_ symbology: VNBarcodeSymbology) -> String {
        switch symbology {
        case .qr: return "QR"
        case .aztec: return "Aztec"
        case .pdf417: return "PDF417"
        case .dataMatrix: return "Data Matrix"
        case .ean8: return "EAN-8"
        case .ean13: return "EAN-13"
        case .upce: return "UPC-E"
        case .code39: return "Code 39"
        case .code93: return "Code 93"
        case .code128: return "Code 128"
        case .itf14: return "ITF-14"
        case .i2of5: return "Interleaved 2 of 5"
        default:
            return prettyLabel(symbology.rawValue)
        }
    }

    /// Maps UI device orientation + front/back camera to Vision’s image orientation.
    static func visionOrientation(
        deviceOrientation: UIDeviceOrientation,
        cameraPosition: AVCaptureDevice.Position
    ) -> CGImagePropertyOrientation {
        let isFront = cameraPosition == .front
        switch deviceOrientation {
        case .portrait:
            return isFront ? .leftMirrored : .right
        case .portraitUpsideDown:
            return isFront ? .rightMirrored : .left
        case .landscapeLeft:
            // Home button / island on the right when holding landscape-left.
            return isFront ? .downMirrored : .up
        case .landscapeRight:
            return isFront ? .upMirrored : .down
        default:
            return isFront ? .leftMirrored : .right
        }
    }
}
