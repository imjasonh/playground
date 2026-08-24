import UIKit
import XCTest
@testable import Playground

final class DoomFaceTests: XCTestCase {
    func testSheetListsFortyTwoSlots() {
        // 5 health rows × 8 expressions + god + dead
        XCTAssertEqual(DoomFaceSheetLayout.allSlots.count, 42)
    }

    func testPerHealthRectsStayOnSheet() {
        let sheet = CGRect(origin: .zero, size: DoomFaceSheetLayout.sheetSize)
        for slot in DoomFaceSheetLayout.allSlots {
            let rect = DoomFaceSheetLayout.rect(for: slot)
            XCTAssertFalse(rect.isEmpty, slot.id)
            XCTAssertTrue(sheet.contains(rect), "\(slot.id) \(rect) escapes sheet")
            XCTAssertEqual(rect.width, DoomFaceSheetLayout.faceSize.width, accuracy: 0.5)
            XCTAssertEqual(rect.height, DoomFaceSheetLayout.faceSize.height, accuracy: 0.5)
        }
    }

    func testGodAndDeadAreUniqueSpecials() {
        let god = DoomFaceSheetLayout.rect(for: DoomFaceSlot(health: nil, expression: .god))
        let dead = DoomFaceSheetLayout.rect(for: DoomFaceSlot(health: nil, expression: .dead))
        XCTAssertEqual(god.origin.x, 20, accuracy: 0.5)
        XCTAssertEqual(dead.origin.x, 560, accuracy: 0.5)
        XCTAssertFalse(god.intersects(dead))
    }

    func testNextEmptySlotWalksHealthRows() {
        var filled: Set<DoomFaceSlot> = []
        let first = DoomFaceSheetLayout.nextEmptySlot(for: .lookCenter, filled: filled)
        XCTAssertEqual(first?.health, 0)

        filled.insert(DoomFaceSlot(health: 0, expression: .lookCenter))
        let second = DoomFaceSheetLayout.nextEmptySlot(for: .lookCenter, filled: filled)
        XCTAssertEqual(second?.health, 1)

        for health in 0..<DoomFaceSheetLayout.healthRowCount {
            filled.insert(DoomFaceSlot(health: health, expression: .lookCenter))
        }
        XCTAssertNil(DoomFaceSheetLayout.nextEmptySlot(for: .lookCenter, filled: filled))
    }

    func testMatcherClassifiesLookSmileOuchAndSpecials() {
        var sample = DoomFaceBlendSample.zero
        sample.lookLeft = 0.4
        XCTAssertEqual(DoomFaceMatcher.match(sample), .lookLeft)

        sample = .zero
        sample.lookRight = 0.65
        XCTAssertEqual(DoomFaceMatcher.match(sample), .turnRight)

        sample = .zero
        sample.jawOpen = 0.6
        XCTAssertEqual(DoomFaceMatcher.match(sample), .ouch)

        sample = .zero
        sample.smile = 0.7
        XCTAssertEqual(DoomFaceMatcher.match(sample), .evil)

        sample = .zero
        sample.browDown = 0.55
        XCTAssertEqual(DoomFaceMatcher.match(sample), .kill)

        sample = .zero
        sample.eyeWide = 0.7
        XCTAssertEqual(DoomFaceMatcher.match(sample), .god)

        sample = .zero
        sample.eyeBlink = 0.95
        XCTAssertEqual(DoomFaceMatcher.match(sample), .dead)

        sample = .zero
        XCTAssertEqual(DoomFaceMatcher.match(sample), .lookCenter)
    }

    func testHoldTrackerRequiresStableDuration() {
        var tracker = DoomFaceMatcher.HoldTracker()
        let t0 = Date(timeIntervalSince1970: 1_000)
        XCTAssertNil(tracker.update(.lookLeft, now: t0, holdDuration: 0.5, cooldown: 1))
        XCTAssertNil(tracker.update(.lookLeft, now: t0.addingTimeInterval(0.2), holdDuration: 0.5, cooldown: 1))
        XCTAssertEqual(
            tracker.update(.lookLeft, now: t0.addingTimeInterval(0.55), holdDuration: 0.5, cooldown: 1),
            .lookLeft
        )
        // Cooldown blocks an immediate second capture.
        XCTAssertNil(tracker.update(.lookLeft, now: t0.addingTimeInterval(0.8), holdDuration: 0.5, cooldown: 1))
    }

    func testHoldTrackerResetsWhenExpressionChanges() {
        var tracker = DoomFaceMatcher.HoldTracker()
        let t0 = Date(timeIntervalSince1970: 2_000)
        XCTAssertNil(tracker.update(.ouch, now: t0, holdDuration: 0.5, cooldown: 1))
        XCTAssertNil(tracker.update(.evil, now: t0.addingTimeInterval(0.4), holdDuration: 0.5, cooldown: 1))
        XCTAssertNil(tracker.update(.evil, now: t0.addingTimeInterval(0.7), holdDuration: 0.5, cooldown: 1))
        XCTAssertEqual(
            tracker.update(.evil, now: t0.addingTimeInterval(1.0), holdDuration: 0.5, cooldown: 1),
            .evil
        )
    }

    func testGIFIdleSequencePrefersLookCycle() throws {
        let left = solidImage(color: .red)
        let center = solidImage(color: .green)
        let right = solidImage(color: .blue)
        let captures: [DoomFaceSlot: UIImage] = [
            DoomFaceSlot(health: 0, expression: .lookLeft): left,
            DoomFaceSlot(health: 0, expression: .lookCenter): center,
            DoomFaceSlot(health: 0, expression: .lookRight): right,
            DoomFaceSlot(health: 0, expression: .evil): solidImage(color: .yellow),
        ]

        let frames = DoomFaceGIFExporter.frames(from: captures)
        XCTAssertEqual(frames.count, 4)
        XCTAssertEqual(averageRed(frames[0]), 1, accuracy: 0.05)
        XCTAssertEqual(averageRed(frames[1]), 0, accuracy: 0.05)
        XCTAssertEqual(averageRed(frames[2]), 0, accuracy: 0.05)
        XCTAssertEqual(averageRed(frames[3]), 0, accuracy: 0.05)
        // Frame 1 and 3 are both center (green → low red).
        XCTAssertEqual(averageGreen(frames[1]), 1, accuracy: 0.05)
        XCTAssertEqual(averageGreen(frames[3]), 1, accuracy: 0.05)

        let data = try XCTUnwrap(DoomFaceGIFExporter.makeGIF(captures: captures))
        XCTAssertGreaterThan(data.count, 32)
        XCTAssertEqual(Array(data.prefix(6)), [0x47, 0x49, 0x46, 0x38, 0x39, 0x61]) // GIF89a
    }

    func testGIFNeedsAtLeastTwoFrames() {
        let captures = [DoomFaceSlot(health: 0, expression: .lookCenter): solidImage(color: .red)]
        XCTAssertNil(DoomFaceGIFExporter.makeGIF(captures: captures))
    }

    func testComposeStampsCapturesOverGreyscale() {
        let size = DoomFaceSheetLayout.sheetSize
        let grey = solidImage(color: .darkGray, size: size)
        let face = solidImage(color: .green, size: DoomFaceSheetLayout.faceSize)
        let slot = DoomFaceSlot(health: 0, expression: .lookCenter)
        let composed = DoomFaceCompositor.compose(
            greyscaleTemplate: grey,
            captures: [slot: face]
        )
        XCTAssertEqual(composed.size, size)
        let rect = DoomFaceSheetLayout.rect(for: slot)
        let sample = pixelColor(composed, at: CGPoint(x: rect.midX, y: rect.midY))
        XCTAssertGreaterThan(sample.g, 0.6)
        XCTAssertLessThan(sample.r, 0.35)
    }

    func testFitFaceMatchesCellSize() {
        let source = solidImage(color: .cyan, size: CGSize(width: 200, height: 300))
        let fitted = DoomFaceCompositor.fitFace(source)
        XCTAssertEqual(fitted.size.width, DoomFaceSheetLayout.faceSize.width, accuracy: 0.5)
        XCTAssertEqual(fitted.size.height, DoomFaceSheetLayout.faceSize.height, accuracy: 0.5)
    }

    func testTemplateAssetExists() {
        XCTAssertNotNil(UIImage(named: "DoomGuyFaces"), "DoomGuyFaces imageset should be in the asset catalog")
    }

    // MARK: - Helpers

    private func solidImage(color: UIColor, size: CGSize = CGSize(width: 24, height: 30)) -> UIImage {
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        return UIGraphicsImageRenderer(size: size, format: format).image { ctx in
            color.setFill()
            ctx.fill(CGRect(origin: .zero, size: size))
        }
    }

    private func averageRed(_ image: UIImage) -> CGFloat {
        averageChannel(image, shift: 16)
    }

    private func averageGreen(_ image: UIImage) -> CGFloat {
        averageChannel(image, shift: 8)
    }

    private func averageChannel(_ image: UIImage, shift: Int) -> CGFloat {
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
        ) else { return -1 }
        context.draw(cgImage, in: CGRect(x: 0, y: 0, width: width, height: height))
        var total: CGFloat = 0
        let count = width * height
        for i in 0..<count {
            total += CGFloat(data[i * 4 + (shift == 16 ? 0 : shift == 8 ? 1 : 2)]) / 255
        }
        return total / CGFloat(count)
    }

    private func pixelColor(_ image: UIImage, at point: CGPoint) -> (r: CGFloat, g: CGFloat, b: CGFloat) {
        guard let cgImage = image.cgImage else { return (0, 0, 0) }
        var pixel = [UInt8](repeating: 0, count: 4)
        let colorSpace = CGColorSpaceCreateDeviceRGB()
        guard let context = CGContext(
            data: &pixel,
            width: 1,
            height: 1,
            bitsPerComponent: 8,
            bytesPerRow: 4,
            space: colorSpace,
            bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
        ) else { return (0, 0, 0) }
        context.translateBy(x: -point.x, y: -point.y)
        context.draw(cgImage, in: CGRect(x: 0, y: 0, width: cgImage.width, height: cgImage.height))
        return (CGFloat(pixel[0]) / 255, CGFloat(pixel[1]) / 255, CGFloat(pixel[2]) / 255)
    }
}
