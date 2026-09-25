import CoreVideo
import Foundation
import Vision

/// On-device OCR for Live Translate. No network.
enum LiveTranslateRecognizer {
    static func recognize(
        pixelBuffer: CVPixelBuffer,
        orientation: CGImagePropertyOrientation
    ) throws -> [LiveTranslateObservation] {
        let handler = VNImageRequestHandler(
            cvPixelBuffer: pixelBuffer,
            orientation: orientation,
            options: [:]
        )
        return try recognize(handler: handler)
    }

    /// Test helper: recognize a CGImage the same way as a live frame.
    static func recognize(
        cgImage: CGImage,
        orientation: CGImagePropertyOrientation = .up
    ) throws -> [LiveTranslateObservation] {
        let handler = VNImageRequestHandler(cgImage: cgImage, orientation: orientation, options: [:])
        return try recognize(handler: handler)
    }

    private static func recognize(handler: VNImageRequestHandler) throws -> [LiveTranslateObservation] {
        let request = VNRecognizeTextRequest()
        request.recognitionLevel = .accurate
        request.usesLanguageCorrection = true
        // The default recognition language is English only, which garbles
        // Japanese, Chinese, or Korean and corrects other text toward English.
        request.automaticallyDetectsLanguage = true
        try handler.perform([request])
        let raw = (request.results ?? []).compactMap { observation -> LiveTranslateObservation? in
            guard let top = observation.topCandidates(1).first else { return nil }
            return LiveTranslateObservation(
                text: top.string,
                confidence: Double(top.confidence),
                boundingBox: observation.boundingBox
            )
        }
        return LiveTranslateResultBuilder.observations(from: raw)
    }
}
