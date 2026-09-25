import CoreGraphics
import Foundation
import Vision

/// On-device OCR for Live Translate. No network.
enum LiveTranslateRecognizer {
    /// Reads the lines in an upright frame, the same image the preview shows.
    static func recognize(cgImage: CGImage) throws -> [LiveTranslateObservation] {
        let handler = VNImageRequestHandler(cgImage: cgImage, orientation: .up, options: [:])
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
