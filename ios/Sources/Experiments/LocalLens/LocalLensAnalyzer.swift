import AVFoundation
import CoreVideo
import Foundation
import UIKit
import Vision

/// Runs one on-device Vision request against a camera frame. No network.
final class LocalLensAnalyzer {
    /// Minimum joint confidence before drawing a pose point.
    static let jointConfidenceThreshold: Float = 0.2

    func analyze(pixelBuffer: CVPixelBuffer, mode: LocalLensMode, orientation: CGImagePropertyOrientation) throws -> LocalLensFrameResult {
        let handler = VNImageRequestHandler(cvPixelBuffer: pixelBuffer, orientation: orientation, options: [:])
        return try analyze(handler: handler, mode: mode)
    }

    /// Test helper: analyze a CGImage the same way as a live frame.
    func analyze(cgImage: CGImage, mode: LocalLensMode, orientation: CGImagePropertyOrientation = .up) throws -> LocalLensFrameResult {
        let handler = VNImageRequestHandler(cgImage: cgImage, orientation: orientation, options: [:])
        return try analyze(handler: handler, mode: mode)
    }

    private func analyze(handler: VNImageRequestHandler, mode: LocalLensMode) throws -> LocalLensFrameResult {
        switch mode {
        case .classify:
            return try classify(handler: handler)
        case .text:
            return try recognizeText(handler: handler)
        case .animals:
            return try recognizeAnimals(handler: handler)
        case .faces:
            return try detectFaceLandmarks(handler: handler)
        case .people:
            return try detectPeople(handler: handler)
        case .body:
            return try detectBodyPose(handler: handler)
        case .hands:
            return try detectHandPose(handler: handler)
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

    private func detectFaceLandmarks(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNDetectFaceLandmarksRequest()
        try handler.perform([request])

        var findings: [LocalLensFinding] = []
        var joints: [CGPoint] = []
        var bones: [LocalLensBone] = []

        for (index, observation) in (request.results ?? []).enumerated() {
            let faceNumber = index + 1
            findings.append(
                LocalLensFinding(
                    label: "Face \(faceNumber)",
                    confidence: Double(observation.confidence),
                    boundingBox: observation.boundingBox
                )
            )

            guard let landmarks = observation.landmarks else { continue }

            let regions: [(String, VNFaceLandmarkRegion2D?)] = [
                ("Contour", landmarks.faceContour),
                ("Left eye", landmarks.leftEye),
                ("Right eye", landmarks.rightEye),
                ("Left pupil", landmarks.leftPupil),
                ("Right pupil", landmarks.rightPupil),
                ("Nose", landmarks.nose),
                ("Outer lips", landmarks.outerLips),
            ]

            for (name, region) in regions {
                guard let region else { continue }
                let points = Self.imagePoints(from: region, faceBox: observation.boundingBox)
                guard !points.isEmpty else { continue }

                joints.append(contentsOf: points)
                bones.append(contentsOf: Self.polylineBones(points, closed: name == "Left eye" || name == "Right eye" || name == "Outer lips" || name == "Contour"))

                if name.contains("eye") || name.contains("pupil") {
                    findings.append(
                        LocalLensFinding(
                            label: "Face \(faceNumber) \(name.lowercased())",
                            confidence: Double(observation.confidence),
                            boundingBox: Self.boundingBox(containing: points)
                        )
                    )
                }
            }
        }

        return LocalLensResultBuilder.build(
            mode: .faces,
            findings: findings,
            joints: joints,
            bones: bones,
            minimumConfidence: 0.15,
            maxFindings: 10
        )
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

    private func detectBodyPose(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNDetectHumanBodyPoseRequest()
        // Some simulators cannot load the body-pose model (Vision Code=9).
        // Treat that as “nothing found” so Local Lens still runs elsewhere.
        do {
            try handler.perform([request])
        } catch {
            if Self.isUnavailableVisionRequest(error) {
                return .empty(mode: .body)
            }
            throw error
        }

        var findings: [LocalLensFinding] = []
        var joints: [CGPoint] = []
        var bones: [LocalLensBone] = []

        for (index, observation) in (request.results ?? []).enumerated() {
            let recognized = (try? observation.recognizedPoints(.all)) ?? [:]
            let usable = recognized.filter { $0.value.confidence >= Self.jointConfidenceThreshold }
            guard !usable.isEmpty else { continue }

            let pointsByJoint = Dictionary(uniqueKeysWithValues: usable.map { ($0.key, $0.value.location) })
            let confidences = usable.map { Double($0.value.confidence) }
            let avg = LocalLensResultBuilder.averageConfidence(of: confidences)

            joints.append(contentsOf: pointsByJoint.values)
            bones.append(contentsOf: Self.bodyBones(from: pointsByJoint))

            findings.append(
                LocalLensFinding(
                    label: "Body \(index + 1) · \(pointsByJoint.count) joints",
                    confidence: avg,
                    boundingBox: Self.boundingBox(containing: Array(pointsByJoint.values))
                )
            )
        }

        return LocalLensResultBuilder.build(
            mode: .body,
            findings: findings,
            joints: joints,
            bones: bones,
            minimumConfidence: 0.15
        )
    }

    private func detectHandPose(handler: VNImageRequestHandler) throws -> LocalLensFrameResult {
        let request = VNDetectHumanHandPoseRequest()
        request.maximumHandCount = 2
        do {
            try handler.perform([request])
        } catch {
            if Self.isUnavailableVisionRequest(error) {
                return .empty(mode: .hands)
            }
            throw error
        }

        var findings: [LocalLensFinding] = []
        var joints: [CGPoint] = []
        var bones: [LocalLensBone] = []

        for (index, observation) in (request.results ?? []).enumerated() {
            let recognized = (try? observation.recognizedPoints(.all)) ?? [:]
            let usable = recognized.filter { $0.value.confidence >= Self.jointConfidenceThreshold }
            guard !usable.isEmpty else { continue }

            let pointsByJoint = Dictionary(uniqueKeysWithValues: usable.map { ($0.key, $0.value.location) })
            let confidences = usable.map { Double($0.value.confidence) }
            let avg = LocalLensResultBuilder.averageConfidence(of: confidences)

            joints.append(contentsOf: pointsByJoint.values)
            bones.append(contentsOf: Self.handBones(from: pointsByJoint))

            let side: String
            switch observation.chirality {
            case .left: side = "Left hand"
            case .right: side = "Right hand"
            default: side = "Hand \(index + 1)"
            }

            findings.append(
                LocalLensFinding(
                    label: "\(side) · \(pointsByJoint.count) pts",
                    confidence: avg,
                    boundingBox: Self.boundingBox(containing: Array(pointsByJoint.values))
                )
            )
        }

        return LocalLensResultBuilder.build(
            mode: .hands,
            findings: findings,
            joints: joints,
            bones: bones,
            minimumConfidence: 0.15
        )
    }

    /// Vision Code=9 ("Unable to setup request") shows up on some simulator
    /// runtimes that lack the pose model / Neural Engine path.
    static func isUnavailableVisionRequest(_ error: Error) -> Bool {
        let nsError = error as NSError
        if nsError.domain == "com.apple.Vision", nsError.code == 9 {
            return true
        }
        let text = nsError.localizedDescription.lowercased()
        return text.contains("unable to setup request")
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

    // MARK: - Geometry helpers

    /// Face landmark points are normalized within the face bounding box.
    static func imagePoints(from region: VNFaceLandmarkRegion2D, faceBox: CGRect) -> [CGPoint] {
        region.normalizedPoints.map { point in
            CGPoint(
                x: faceBox.origin.x + point.x * faceBox.width,
                y: faceBox.origin.y + point.y * faceBox.height
            )
        }
    }

    static func polylineBones(_ points: [CGPoint], closed: Bool) -> [LocalLensBone] {
        guard points.count >= 2 else { return [] }
        var bones: [LocalLensBone] = []
        for index in 0..<(points.count - 1) {
            bones.append(LocalLensBone(from: points[index], to: points[index + 1]))
        }
        if closed, let first = points.first, let last = points.last, points.count > 2 {
            bones.append(LocalLensBone(from: last, to: first))
        }
        return bones
    }

    static func boundingBox(containing points: [CGPoint]) -> CGRect? {
        guard let first = points.first else { return nil }
        var minX = first.x
        var maxX = first.x
        var minY = first.y
        var maxY = first.y
        for point in points.dropFirst() {
            minX = min(minX, point.x)
            maxX = max(maxX, point.x)
            minY = min(minY, point.y)
            maxY = max(maxY, point.y)
        }
        return CGRect(x: minX, y: minY, width: max(maxX - minX, 0.01), height: max(maxY - minY, 0.01))
    }

    static func bodyBones(
        from points: [VNHumanBodyPoseObservation.JointName: CGPoint]
    ) -> [LocalLensBone] {
        let pairs: [(VNHumanBodyPoseObservation.JointName, VNHumanBodyPoseObservation.JointName)] = [
            (.nose, .neck),
            (.neck, .leftShoulder),
            (.neck, .rightShoulder),
            (.leftShoulder, .leftElbow),
            (.leftElbow, .leftWrist),
            (.rightShoulder, .rightElbow),
            (.rightElbow, .rightWrist),
            (.neck, .root),
            (.root, .leftHip),
            (.root, .rightHip),
            (.leftHip, .leftKnee),
            (.leftKnee, .leftAnkle),
            (.rightHip, .rightKnee),
            (.rightKnee, .rightAnkle),
            (.leftShoulder, .rightShoulder),
            (.leftHip, .rightHip),
            (.leftEye, .rightEye),
            (.leftEye, .nose),
            (.rightEye, .nose),
            (.leftEar, .leftEye),
            (.rightEar, .rightEye),
        ]
        return bones(from: points, pairs: pairs)
    }

    static func handBones(
        from points: [VNHumanHandPoseObservation.JointName: CGPoint]
    ) -> [LocalLensBone] {
        let pairs: [(VNHumanHandPoseObservation.JointName, VNHumanHandPoseObservation.JointName)] = [
            (.wrist, .thumbCMC),
            (.thumbCMC, .thumbMP),
            (.thumbMP, .thumbIP),
            (.thumbIP, .thumbTip),
            (.wrist, .indexMCP),
            (.indexMCP, .indexPIP),
            (.indexPIP, .indexDIP),
            (.indexDIP, .indexTip),
            (.wrist, .middleMCP),
            (.middleMCP, .middlePIP),
            (.middlePIP, .middleDIP),
            (.middleDIP, .middleTip),
            (.wrist, .ringMCP),
            (.ringMCP, .ringPIP),
            (.ringPIP, .ringDIP),
            (.ringDIP, .ringTip),
            (.wrist, .littleMCP),
            (.littleMCP, .littlePIP),
            (.littlePIP, .littleDIP),
            (.littleDIP, .littleTip),
            (.indexMCP, .middleMCP),
            (.middleMCP, .ringMCP),
            (.ringMCP, .littleMCP),
        ]
        return bones(from: points, pairs: pairs)
    }

    private static func bones<Joint: Hashable>(
        from points: [Joint: CGPoint],
        pairs: [(Joint, Joint)]
    ) -> [LocalLensBone] {
        pairs.compactMap { a, b in
            guard let from = points[a], let to = points[b] else { return nil }
            return LocalLensBone(from: from, to: to)
        }
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
        LocalLensCoordinateMapper.visionOrientation(
            deviceOrientation: deviceOrientation,
            cameraPosition: cameraPosition
        )
    }
}
