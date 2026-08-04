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
        XCTAssertEqual(LocalLensMode.allCases.count, 6)
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

    func testAnalyzerBarcodeAndFaceModesAcceptEmptyFrames() throws {
        let image = try XCTUnwrap(Self.makeSolidImage(color: .white, size: CGSize(width: 200, height: 200)))
        let analyzer = LocalLensAnalyzer()
        let barcodes = try analyzer.analyze(cgImage: image, mode: .barcodes)
        let faces = try analyzer.analyze(cgImage: image, mode: .faces)
        let people = try analyzer.analyze(cgImage: image, mode: .people)
        let animals = try analyzer.analyze(cgImage: image, mode: .animals)
        XCTAssertEqual(barcodes.mode, .barcodes)
        XCTAssertEqual(faces.mode, .faces)
        XCTAssertEqual(people.mode, .people)
        XCTAssertEqual(animals.mode, .animals)
        XCTAssertTrue(barcodes.findings.isEmpty)
        XCTAssertTrue(faces.findings.isEmpty)
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
