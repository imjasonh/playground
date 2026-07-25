import UIKit
import XCTest
@testable import Playground

final class ViewMasterStereoTests: XCTestCase {
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
            StereoPairAligner.makePair(wide: wide, ultraWide: ultra, swapEyes: false)
        )
        XCTAssertEqual(normal.left.size, wide.size)
        XCTAssertEqual(normal.right.size, wide.size)
        XCTAssertEqual(averageRed(normal.right), 1, accuracy: 0.05)
        XCTAssertEqual(averageRed(normal.left), 0, accuracy: 0.05)

        let swapped = try XCTUnwrap(
            StereoPairAligner.makePair(wide: wide, ultraWide: ultra, swapEyes: true)
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
