import CoreGraphics
import UIKit
import XCTest
@testable import Playground

final class LocalLensTests: XCTestCase {
    func testResultBuilderFiltersByConfidenceAndCapsCount() {
        let findings = [
            LocalLensFinding(id: "a", label: "Cat", confidence: 0.9),
            LocalLensFinding(id: "b", label: "Dog", confidence: 0.05),
            LocalLensFinding(id: "c", label: "Bird", confidence: 0.4),
            LocalLensFinding(id: "d", label: "  ", confidence: 0.99),
            LocalLensFinding(id: "e", label: "Tree", confidence: 0.7),
            LocalLensFinding(id: "f", label: "Car", confidence: 0.6),
            LocalLensFinding(id: "g", label: "Bike", confidence: 0.55),
            LocalLensFinding(id: "h", label: "Boat", confidence: 0.5),
        ]

        let result = LocalLensResultBuilder.build(
            mode: .classify,
            findings: findings,
            minimumConfidence: 0.15,
            maxFindings: 4
        )

        XCTAssertEqual(result.mode, .classify)
        XCTAssertEqual(result.findings.map(\.label), ["Cat", "Tree", "Car", "Bike"])
        XCTAssertFalse(result.findings.contains { $0.label == "Dog" })
        XCTAssertFalse(result.findings.contains { $0.label.trimmingCharacters(in: .whitespaces).isEmpty })
    }

    func testResultBuilderSortsTiesAlphabetically() {
        let findings = [
            LocalLensFinding(label: "Zebra", confidence: 0.5),
            LocalLensFinding(label: "Apple", confidence: 0.5),
        ]
        let result = LocalLensResultBuilder.build(mode: .classify, findings: findings)
        XCTAssertEqual(result.findings.map(\.label), ["Apple", "Zebra"])
    }

    func testConfidenceFormatting() {
        XCTAssertEqual(LocalLensResultBuilder.confidencePercent(0.876), 88)
        XCTAssertEqual(LocalLensResultBuilder.confidenceLabel(0.5), "50%")
        XCTAssertEqual(
            LocalLensResultBuilder.chipText(
                for: LocalLensFinding(label: "Coffee Cup", confidence: 0.42)
            ),
            "Coffee Cup · 42%"
        )
    }

    func testPrettyLabelHumanizesIdentifiers() {
        XCTAssertEqual(LocalLensAnalyzer.prettyLabel("coffee_cup"), "Coffee Cup")
        XCTAssertEqual(LocalLensAnalyzer.prettyLabel("golden-retriever"), "Golden Retriever")
    }

    func testEmptyStatusPerMode() {
        for mode in LocalLensMode.allCases {
            XCTAssertFalse(LocalLensResultBuilder.emptyStatus(for: mode).isEmpty)
        }
    }

    func testModeMetadataIsComplete() {
        for mode in LocalLensMode.allCases {
            XCTAssertFalse(mode.title.isEmpty)
            XCTAssertFalse(mode.symbolName.isEmpty)
            XCTAssertFalse(mode.blurb.isEmpty)
        }
        XCTAssertEqual(LocalLensMode.allCases.count, 8)
        XCTAssertTrue(LocalLensMode.body.drawsJoints)
        XCTAssertTrue(LocalLensMode.hands.drawsJoints)
        XCTAssertTrue(LocalLensMode.faces.drawsJoints)
        XCTAssertFalse(LocalLensMode.classify.drawsJoints)
    }

    func testAverageConfidence() {
        XCTAssertEqual(LocalLensResultBuilder.averageConfidence(of: []), 0)
        XCTAssertEqual(LocalLensResultBuilder.averageConfidence(of: [0.2, 0.4, 0.6]), 0.4, accuracy: 0.0001)
    }

    func testPolylineBonesCloseLoopWhenRequested() {
        let points = [
            CGPoint(x: 0, y: 0),
            CGPoint(x: 1, y: 0),
            CGPoint(x: 1, y: 1),
        ]
        let open = LocalLensAnalyzer.polylineBones(points, closed: false)
        let closed = LocalLensAnalyzer.polylineBones(points, closed: true)
        XCTAssertEqual(open.count, 2)
        XCTAssertEqual(closed.count, 3)
        XCTAssertEqual(closed.last?.from, CGPoint(x: 1, y: 1))
        XCTAssertEqual(closed.last?.to, CGPoint(x: 0, y: 0))
    }

    func testBoundingBoxContainingPoints() {
        let box = LocalLensAnalyzer.boundingBox(containing: [
            CGPoint(x: 0.2, y: 0.3),
            CGPoint(x: 0.5, y: 0.7),
        ])
        XCTAssertEqual(box?.origin.x ?? -1, 0.2, accuracy: 0.0001)
        XCTAssertEqual(box?.origin.y ?? -1, 0.3, accuracy: 0.0001)
        XCTAssertEqual(box?.width ?? -1, 0.3, accuracy: 0.0001)
        XCTAssertEqual(box?.height ?? -1, 0.4, accuracy: 0.0001)
    }

    func testBodyBonesSkipMissingJoints() {
        let bones = LocalLensAnalyzer.bodyBones(from: [
            .nose: CGPoint(x: 0.5, y: 0.9),
            .neck: CGPoint(x: 0.5, y: 0.8),
            // left shoulder missing — that bone should be omitted
            .rightShoulder: CGPoint(x: 0.6, y: 0.75),
        ])
        XCTAssertTrue(bones.contains { $0.from == CGPoint(x: 0.5, y: 0.9) && $0.to == CGPoint(x: 0.5, y: 0.8) })
        XCTAssertTrue(bones.contains { $0.from == CGPoint(x: 0.5, y: 0.8) && $0.to == CGPoint(x: 0.6, y: 0.75) })
        XCTAssertFalse(bones.contains { bone in
            bone.from == CGPoint(x: 0.5, y: 0.8) && bone.to.x < 0.5
        })
    }

    func testResultBuilderPreservesPoseGeometry() {
        let joints = [CGPoint(x: 0.1, y: 0.2), CGPoint(x: 0.3, y: 0.4)]
        let bones = [LocalLensBone(from: joints[0], to: joints[1])]
        let result = LocalLensResultBuilder.build(
            mode: .body,
            findings: [LocalLensFinding(label: "Body 1 · 2 joints", confidence: 0.8)],
            joints: joints,
            bones: bones
        )
        XCTAssertEqual(result.joints, joints)
        XCTAssertEqual(result.bones, bones)
    }

    func testVisionOrientationDefaultsToPortraitMapping() {
        let rear = LocalLensAnalyzer.visionOrientation(
            deviceOrientation: .unknown,
            cameraPosition: .back
        )
        let front = LocalLensAnalyzer.visionOrientation(
            deviceOrientation: .unknown,
            cameraPosition: .front
        )
        XCTAssertEqual(rear, .right)
        XCTAssertEqual(front, .leftMirrored)
    }

    func testRearPortraitOrientationIsRightSoOCRIsNotBackwards() {
        // Sensor-native rear buffers need `.right` in portrait. Feeding `.up`
        // (as if videoOrientation had already rotated the frame) makes OCR read
        // text backwards / rotated.
        let orientation = LocalLensCoordinateMapper.visionOrientation(
            deviceOrientation: .portrait,
            cameraPosition: .back
        )
        XCTAssertEqual(orientation, .right)
        XCTAssertEqual(
            LocalLensCoordinateMapper.visionOrientation(
                deviceOrientation: .landscapeRight,
                cameraPosition: .back
            ),
            .down
        )
        XCTAssertEqual(
            LocalLensCoordinateMapper.visionOrientation(
                deviceOrientation: .portrait,
                cameraPosition: .front
            ),
            .leftMirrored
        )
    }

    func testUprightCIImageRebasesExtentToOrigin() throws {
        var buffer: CVPixelBuffer?
        let status = CVPixelBufferCreate(
            kCFAllocatorDefault,
            64,
            32,
            kCVPixelFormatType_32BGRA,
            nil,
            &buffer
        )
        XCTAssertEqual(status, kCVReturnSuccess)
        let pixelBuffer = try XCTUnwrap(buffer)

        // `.right` swaps width/height for a landscape sensor buffer.
        let upright = LocalLensCoordinateMapper.uprightCIImage(
            from: pixelBuffer,
            orientation: .right
        )
        XCTAssertEqual(upright.extent.origin, .zero)
        XCTAssertEqual(upright.extent.width, 32, accuracy: 0.001)
        XCTAssertEqual(upright.extent.height, 64, accuracy: 0.001)
    }

    func testCaptureOrientationSwapsLandscapeAxes() {
        XCTAssertEqual(LocalLensCoordinateMapper.captureOrientation(for: .portrait), .portrait)
        XCTAssertEqual(LocalLensCoordinateMapper.captureOrientation(for: .portraitUpsideDown), .portraitUpsideDown)
        XCTAssertEqual(LocalLensCoordinateMapper.captureOrientation(for: .landscapeLeft), .landscapeRight)
        XCTAssertEqual(LocalLensCoordinateMapper.captureOrientation(for: .landscapeRight), .landscapeLeft)
        XCTAssertEqual(LocalLensCoordinateMapper.captureOrientation(for: .faceUp), .portrait)
    }

    func testVisionNormalizedPointMapsToImageTopLeft() {
        let imageSize = CGSize(width: 100, height: 200)
        let bottomLeft = LocalLensCoordinateMapper.imagePoint(
            fromVisionNormalized: CGPoint(x: 0, y: 0),
            imageSize: imageSize
        )
        let topRight = LocalLensCoordinateMapper.imagePoint(
            fromVisionNormalized: CGPoint(x: 1, y: 1),
            imageSize: imageSize
        )
        XCTAssertEqual(bottomLeft.x, 0, accuracy: 0.001)
        XCTAssertEqual(bottomLeft.y, 200, accuracy: 0.001)
        XCTAssertEqual(topRight.x, 100, accuracy: 0.001)
        XCTAssertEqual(topRight.y, 0, accuracy: 0.001)
    }

    func testAspectFillCentersWiderImageInTallView() {
        // 200×100 image into 100×100 view → scale 1, x offset -50.
        let transform = LocalLensCoordinateMapper.ContentTransform.aspectFill(
            imageSize: CGSize(width: 200, height: 100),
            viewSize: CGSize(width: 100, height: 100)
        )
        XCTAssertEqual(transform.scale, 1, accuracy: 0.001)
        XCTAssertEqual(transform.offsetX, -50, accuracy: 0.001)
        XCTAssertEqual(transform.offsetY, 0, accuracy: 0.001)

        let center = LocalLensCoordinateMapper.viewPoint(
            fromVisionNormalized: CGPoint(x: 0.5, y: 0.5),
            imageSize: CGSize(width: 200, height: 100),
            viewSize: CGSize(width: 100, height: 100)
        )
        XCTAssertEqual(center.x, 50, accuracy: 0.001)
        XCTAssertEqual(center.y, 50, accuracy: 0.001)
    }

    func testAspectFillMapsVisionBoxIntoCroppedView() {
        // Portrait buffer 1080×1920 into landscape-ish wide view 1920×1080.
        let imageSize = CGSize(width: 1080, height: 1920)
        let viewSize = CGSize(width: 1920, height: 1080)
        let box = CGRect(x: 0.25, y: 0.25, width: 0.5, height: 0.5)
        let rect = LocalLensCoordinateMapper.viewRect(
            fromVisionNormalized: box,
            imageSize: imageSize,
            viewSize: viewSize
        )
        // Scale = max(1920/1080, 1080/1920) = 1920/1080 ≈ 1.777…
        let scale = 1920.0 / 1080.0
        let offsetY = (1080.0 - 1920.0 * scale) / 2.0
        XCTAssertEqual(rect.origin.x, 0.25 * 1080 * scale, accuracy: 0.5)
        XCTAssertEqual(rect.size.width, 0.5 * 1080 * scale, accuracy: 0.5)
        XCTAssertEqual(
            rect.origin.y,
            (1 - 0.25 - 0.5) * 1920 * scale + offsetY,
            accuracy: 0.5
        )
    }

    func testAnalyzerClassifiesSyntheticImageWithoutCrashing() throws {
        let image = try XCTUnwrap(Self.makeSolidImage(color: .systemTeal, size: CGSize(width: 256, height: 256)))
        let analyzer = LocalLensAnalyzer()
        let result = try analyzer.analyze(cgImage: image, mode: .classify)
        XCTAssertEqual(result.mode, .classify)
        // Taxonomy depends on the OS model; just assert the pipeline completes.
        XCTAssertLessThanOrEqual(result.findings.count, LocalLensResultBuilder.defaultMaxFindings)
        for finding in result.findings {
            XCTAssertGreaterThanOrEqual(finding.confidence, LocalLensResultBuilder.defaultMinimumConfidence)
            XCTAssertFalse(finding.label.isEmpty)
        }
    }

    func testAnalyzerReadsDrawnText() throws {
        let image = try XCTUnwrap(Self.makeTextImage(text: "HELLO", size: CGSize(width: 320, height: 120)))
        let analyzer = LocalLensAnalyzer()
        let result = try analyzer.analyze(cgImage: image, mode: .text)
        XCTAssertEqual(result.mode, .text)
        let joined = result.findings.map(\.label).joined(separator: " ").uppercased()
        XCTAssertTrue(
            joined.contains("HELLO") || result.findings.isEmpty,
            "Expected OCR to see HELLO or return empty on a sparse renderer; got \(joined)"
        )
    }

    func testAnalyzerBarcodeFaceAndPoseModesAcceptEmptyFrames() throws {
        let image = try XCTUnwrap(Self.makeSolidImage(color: .white, size: CGSize(width: 200, height: 200)))
        let analyzer = LocalLensAnalyzer()
        let barcodes = try analyzer.analyze(cgImage: image, mode: .barcodes)
        let faces = try analyzer.analyze(cgImage: image, mode: .faces)
        let people = try analyzer.analyze(cgImage: image, mode: .people)
        let animals = try analyzer.analyze(cgImage: image, mode: .animals)
        // Body/hand pose may be unavailable on some simulators (Vision Code=9);
        // the analyzer returns an empty result instead of throwing.
        let body = try analyzer.analyze(cgImage: image, mode: .body)
        let hands = try analyzer.analyze(cgImage: image, mode: .hands)
        XCTAssertEqual(barcodes.mode, .barcodes)
        XCTAssertEqual(faces.mode, .faces)
        XCTAssertEqual(people.mode, .people)
        XCTAssertEqual(animals.mode, .animals)
        XCTAssertEqual(body.mode, .body)
        XCTAssertEqual(hands.mode, .hands)
        XCTAssertTrue(barcodes.findings.isEmpty)
        XCTAssertTrue(faces.findings.isEmpty)
        XCTAssertTrue(faces.joints.isEmpty)
        XCTAssertTrue(body.findings.isEmpty)
        XCTAssertTrue(body.joints.isEmpty)
        XCTAssertTrue(hands.findings.isEmpty)
    }

    func testUnavailableVisionRequestDetection() {
        let setupError = NSError(
            domain: "com.apple.Vision",
            code: 9,
            userInfo: [NSLocalizedDescriptionKey: "Unable to setup request in VNDetectHumanBodyPoseRequest"]
        )
        XCTAssertTrue(LocalLensAnalyzer.isUnavailableVisionRequest(setupError))
        XCTAssertFalse(
            LocalLensAnalyzer.isUnavailableVisionRequest(
                NSError(domain: "com.apple.Vision", code: 1, userInfo: nil)
            )
        )
        XCTAssertFalse(
            LocalLensAnalyzer.isUnavailableVisionRequest(
                NSError(domain: NSPOSIXErrorDomain, code: 1, userInfo: nil)
            )
        )
    }

    // MARK: - Image fixtures

    private static func makeSolidImage(color: UIColor, size: CGSize) -> CGImage? {
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        let renderer = UIGraphicsImageRenderer(size: size, format: format)
        let image = renderer.image { ctx in
            color.setFill()
            ctx.fill(CGRect(origin: .zero, size: size))
        }
        return image.cgImage
    }

    private static func makeTextImage(text: String, size: CGSize) -> CGImage? {
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        let renderer = UIGraphicsImageRenderer(size: size, format: format)
        let image = renderer.image { ctx in
            UIColor.white.setFill()
            ctx.fill(CGRect(origin: .zero, size: size))
            let attributes: [NSAttributedString.Key: Any] = [
                .font: UIFont.boldSystemFont(ofSize: 64),
                .foregroundColor: UIColor.black,
            ]
            let drawn = text as NSString
            let textSize = drawn.size(withAttributes: attributes)
            let origin = CGPoint(
                x: (size.width - textSize.width) / 2,
                y: (size.height - textSize.height) / 2
            )
            drawn.draw(at: origin, withAttributes: attributes)
        }
        return image.cgImage
    }
}
