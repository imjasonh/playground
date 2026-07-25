import UIKit
import XCTest
@testable import Playground

final class WigglecamTests: XCTestCase {
    func testPortraitGravityBlocksCapture() {
        let readiness = StereoCaptureGate.evaluate(gravityX: 0, gravityY: -1, gravityZ: 0)
        XCTAssertEqual(readiness.orientation, .portrait)
        XCTAssertFalse(readiness.isLandscape)
        XCTAssertFalse(readiness.canCapture)
        XCTAssertTrue(readiness.blockingReason.lowercased().contains("landscape"))
    }

    func testLevelLandscapeAllowsCapture() {
        let left = StereoCaptureGate.evaluate(gravityX: -0.98, gravityY: 0.05, gravityZ: 0.1)
        XCTAssertEqual(left.orientation, .landscapeRight)
        XCTAssertTrue(left.canCapture)

        let right = StereoCaptureGate.evaluate(gravityX: 0.97, gravityY: -0.08, gravityZ: -0.12)
        XCTAssertEqual(right.orientation, .landscapeLeft)
        XCTAssertTrue(right.canCapture)
    }

    func testPitchedLandscapeBlocksCapture() {
        let readiness = StereoCaptureGate.evaluate(gravityX: 0.85, gravityY: 0.05, gravityZ: 0.52)
        XCTAssertTrue(readiness.isLandscape)
        XCTAssertFalse(readiness.isLevel)
        XCTAssertFalse(readiness.canCapture)
        XCTAssertTrue(readiness.blockingReason.lowercased().contains("level"))
    }

    func testEyeSwapDependsOnLandscapeDirection() {
        XCTAssertFalse(StereoCaptureGate.shouldSwapEyes(for: .landscapeLeft))
        XCTAssertTrue(StereoCaptureGate.shouldSwapEyes(for: .landscapeRight))
        XCTAssertFalse(StereoCaptureGate.shouldSwapEyes(for: .portrait))
    }

    func testCenterCropRetainsTargetSize() throws {
        let source = solidImage(color: .red, size: CGSize(width: 200, height: 100))
        let cropped = try XCTUnwrap(
            StereoPairAligner.centerCrop(
                source,
                zoomFactor: 0.5,
                targetSize: CGSize(width: 80, height: 40)
            )
        )
        XCTAssertEqual(cropped.size.width, 80, accuracy: 0.5)
        XCTAssertEqual(cropped.size.height, 40, accuracy: 0.5)
    }

    func testMakePairMatchesWideSizeAndHonorsSwap() throws {
        let wide = solidImage(color: .red, size: CGSize(width: 120, height: 90))
        let ultra = solidImage(color: .blue, size: CGSize(width: 240, height: 180))

        let normal = try XCTUnwrap(
            StereoPairAligner.makePair(
                wide: wide,
                ultraWide: ultra,
                refineScale: false,
                matchBrightness: false,
                swapEyes: false
            )
        )
        XCTAssertEqual(normal.left.size, wide.size)
        XCTAssertEqual(normal.right.size, wide.size)
        XCTAssertEqual(averageRed(normal.right), 1, accuracy: 0.05)
        XCTAssertEqual(averageRed(normal.left), 0, accuracy: 0.05)

        let swapped = try XCTUnwrap(
            StereoPairAligner.makePair(
                wide: wide,
                ultraWide: ultra,
                refineScale: false,
                matchBrightness: false,
                swapEyes: true
            )
        )
        XCTAssertEqual(averageRed(swapped.left), 1, accuracy: 0.05)
        XCTAssertEqual(averageRed(swapped.right), 0, accuracy: 0.05)
    }

    func testWiggleGIFEncoderProducesGIFData() throws {
        let left = solidImage(color: .red, size: CGSize(width: 64, height: 48))
        let right = solidImage(color: .blue, size: CGSize(width: 64, height: 48))
        let data = try XCTUnwrap(
            WiggleGIFEncoder.makeWiggleGIF(left: left, right: right, maxDimension: 64)
        )
        XCTAssertGreaterThan(data.count, 20)
        // ImageIO may emit GIF87a or GIF89a.
        XCTAssertEqual(Array(data.prefix(4)), Array("GIF8".utf8))
        let version = Array(data.dropFirst(4).prefix(2))
        XCTAssertTrue(version == Array("7a".utf8) || version == Array("9a".utf8))

        let url = try WiggleGIFEncoder.writeTemporaryWiggleGIF(
            left: left,
            right: right,
            maxDimension: 64
        )
        defer { try? FileManager.default.removeItem(at: url) }
        XCTAssertEqual(url.pathExtension.lowercased(), "gif")
        XCTAssertTrue(FileManager.default.fileExists(atPath: url.path))
    }

    func testScaledCGImageCapsLongEdge() throws {
        let image = solidImage(color: .green, size: CGSize(width: 400, height: 200))
        let scaled = try XCTUnwrap(WiggleGIFEncoder.scaledCGImage(from: image, maxDimension: 100))
        XCTAssertEqual(scaled.width, 100)
        XCTAssertEqual(scaled.height, 50)
    }

    func testMatchLuminancePullsMeansTogether() throws {
        let dark = solidImage(color: UIColor(white: 0.25, alpha: 1), size: CGSize(width: 64, height: 64))
        let bright = solidImage(color: UIColor(white: 0.75, alpha: 1), size: CGSize(width: 64, height: 64))
        let beforeDark = try XCTUnwrap(StereoPairAligner.meanLuminance(dark))
        let beforeBright = try XCTUnwrap(StereoPairAligner.meanLuminance(bright))
        XCTAssertGreaterThan(abs(beforeBright - beforeDark), 0.3)

        let matched = StereoPairAligner.matchLuminance(left: dark, right: bright)
        let afterLeft = try XCTUnwrap(StereoPairAligner.meanLuminance(matched.left))
        let afterRight = try XCTUnwrap(StereoPairAligner.meanLuminance(matched.right))
        XCTAssertEqual(afterLeft, afterRight, accuracy: 0.08)
    }

    func testMatchLuminanceIgnoresClippedHighlights() throws {
        // Backlit window: subject midtones differ a lot, but blown sky pulls the
        // whole-frame means closer together — mean matching would under-correct.
        let left = try XCTUnwrap(
            splitToneImage(
                size: 80,
                subjectFraction: 0.75,
                subject: 0.28,
                highlight: 1.0
            )
        )
        let right = try XCTUnwrap(
            splitToneImage(
                size: 80,
                subjectFraction: 0.75,
                subject: 0.52,
                highlight: 0.92
            )
        )

        let beforeLeft = try XCTUnwrap(StereoPairAligner.robustChannelMidtones(left))
        let beforeRight = try XCTUnwrap(StereoPairAligner.robustChannelMidtones(right))
        let beforeGap = abs(beforeLeft.g - beforeRight.g)
        XCTAssertGreaterThan(beforeGap, 0.15)

        let matched = StereoPairAligner.matchLuminance(left: left, right: right)
        let afterLeft = try XCTUnwrap(StereoPairAligner.robustChannelMidtones(matched.left))
        let afterRight = try XCTUnwrap(StereoPairAligner.robustChannelMidtones(matched.right))
        XCTAssertEqual(afterLeft.g, afterRight.g, accuracy: 0.06)
        XCTAssertLessThan(abs(afterLeft.g - afterRight.g), beforeGap * 0.5)
    }

    func testRobustChannelMidtonesSkipsClippedSky() throws {
        let image = try XCTUnwrap(
            splitToneImage(size: 64, subjectFraction: 0.7, subject: 0.3, highlight: 1.0)
        )
        let mids = try XCTUnwrap(StereoPairAligner.robustChannelMidtones(image))
        // Should sit near the subject tone, not halfway to the blown sky.
        XCTAssertEqual(mids.g, 0.3, accuracy: 0.08)
    }

    func testStereoJPEGEncodingProducesTwoPayloads() throws {
        let left = solidImage(color: .red, size: CGSize(width: 32, height: 24))
        let right = solidImage(color: .blue, size: CGSize(width: 32, height: 24))
        let leftData = try XCTUnwrap(left.jpegData(compressionQuality: 0.92))
        let rightData = try XCTUnwrap(right.jpegData(compressionQuality: 0.92))
        XCTAssertGreaterThan(leftData.count, 20)
        XCTAssertGreaterThan(rightData.count, 20)
        // JPEG SOI marker
        XCTAssertEqual(Array(leftData.prefix(2)), [0xFF, 0xD8])
        XCTAssertEqual(Array(rightData.prefix(2)), [0xFF, 0xD8])
    }

    func testCropFactorUsesFOVTangents() {
        let factor = StereoPairAligner.cropFactor(wideFOVDegrees: 70, ultraWideFOVDegrees: 120)
        // tan(35°)/tan(60°) ≈ 0.7003/1.7321 ≈ 0.404
        XCTAssertEqual(factor, 0.404, accuracy: 0.02)
        XCTAssertEqual(
            StereoPairAligner.cropFactor(wideFOVDegrees: 80, ultraWideFOVDegrees: 80),
            StereoPairAligner.defaultUltraWideZoomFactor,
            accuracy: 0.001
        )
    }

    func testRefinedCropFactorMovesTowardTrueScale() throws {
        // Wide: red square on gray. Ultra: same square drawn at 0.5 scale in the center
        // of a 2× canvas (simulating UW), so the correct crop factor is 0.5.
        let wide = try XCTUnwrap(patternImage(size: 80, squareInset: 0.25))
        let ultra = try XCTUnwrap(patternImage(size: 160, squareInset: 0.375))

        let refined = StereoPairAligner.refinedCropFactor(
            wide: wide,
            ultraWide: ultra,
            estimatedFactor: 0.62,
            sampleSize: 48,
            searchFraction: 0.35,
            steps: 11
        )
        XCTAssertEqual(refined, 0.5, accuracy: 0.08)
    }

    // MARK: - Helpers

    private func solidImage(color: UIColor, size: CGSize) -> UIImage {
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        return UIGraphicsImageRenderer(size: size, format: format).image { context in
            color.setFill()
            context.fill(CGRect(origin: .zero, size: size))
        }
    }

    /// Gray canvas with a centered black square. `squareInset` is the margin on
    /// each side as a fraction of the canvas (0.25 → square is half the width).
    private func patternImage(size: CGFloat, squareInset: CGFloat) -> UIImage? {
        let canvas = CGSize(width: size, height: size)
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        return UIGraphicsImageRenderer(size: canvas, format: format).image { _ in
            UIColor.lightGray.setFill()
            UIRectFill(CGRect(origin: .zero, size: canvas))
            let inset = size * squareInset
            UIColor.black.setFill()
            UIRectFill(CGRect(x: inset, y: inset, width: size - inset * 2, height: size - inset * 2))
        }
    }

    /// Top band = highlight (sky), bottom = subject — mimics a backlit window.
    private func splitToneImage(
        size: CGFloat,
        subjectFraction: CGFloat,
        subject: CGFloat,
        highlight: CGFloat
    ) -> UIImage? {
        let canvas = CGSize(width: size, height: size)
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        let subjectHeight = size * min(max(subjectFraction, 0.1), 0.95)
        return UIGraphicsImageRenderer(size: canvas, format: format).image { _ in
            UIColor(white: highlight, alpha: 1).setFill()
            UIRectFill(CGRect(x: 0, y: 0, width: size, height: size - subjectHeight))
            UIColor(white: subject, alpha: 1).setFill()
            UIRectFill(CGRect(x: 0, y: size - subjectHeight, width: size, height: subjectHeight))
        }
    }

    private func averageRed(_ image: UIImage) -> CGFloat {
        guard let cgImage = image.cgImage else { return -1 }
        let width = cgImage.width
        let height = cgImage.height
        var data = [UInt8](repeating: 0, count: width * height * 4)
        let colorSpace = CGColorSpaceCreateDeviceRGB()
        guard let context = CGContext(
            data: &data,
            width: width,
            height: height,
            bitsPerComponent: 8,
            bytesPerRow: width * 4,
            space: colorSpace,
            bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
        ) else {
            return -1
        }
        context.draw(cgImage, in: CGRect(x: 0, y: 0, width: width, height: height))
        var sum: CGFloat = 0
        let count = width * height
        for i in 0..<count {
            sum += CGFloat(data[i * 4]) / 255
        }
        return sum / CGFloat(count)
    }
}
