import CoreImage
import ImageIO
import XCTest
@testable import Playground

final class HairColorTests: XCTestCase {
    func testDyesAreUniqueAndInRange() {
        let ids = HairDye.all.map(\.id)
        XCTAssertEqual(Set(ids).count, ids.count)
        XCTAssertTrue(HairDye.all.contains(HairDye.defaultDye))
        XCTAssertTrue(HairDye.blonde.prefersDarkCheckmark)
        XCTAssertTrue(HairDye.silver.prefersDarkCheckmark)
        XCTAssertFalse(HairDye.jet.prefersDarkCheckmark)
        XCTAssertFalse(HairDye.violet.prefersDarkCheckmark)
        for dye in HairDye.all {
            XCTAssertFalse(dye.id.isEmpty)
            XCTAssertFalse(dye.name.isEmpty)
            for channel in [dye.red, dye.green, dye.blue] {
                XCTAssertGreaterThanOrEqual(channel, 0)
                XCTAssertLessThanOrEqual(channel, 1)
            }
        }
    }

    func testCrownIsHairAndFaceIsNot() {
        let box = CGRect(x: 0.30, y: 0.20, width: 0.40, height: 0.40)
        let region = try XCTUnwrap(
            HairRegionBuilder.region(for: FaceHairGuide(boundingBox: box, hairlineY: nil))
        )
        let hairline = box.maxY - (box.height * HairRegionBuilder.fallbackHairlineInset)
        XCTAssertEqual(region.hairlineY, hairline, accuracy: 0.0001)

        XCTAssertTrue(region.contains(x: 0.50, y: hairline + 0.05))
        XCTAssertFalse(region.contains(x: 0.50, y: box.minY + 0.05))

        let sideburnX = box.minX - (box.width * HairRegionBuilder.sideScale * 0.5)
        let sideburnY = hairline - (box.height * HairRegionBuilder.sideburnScale * 0.5)
        XCTAssertTrue(region.contains(x: sideburnX, y: sideburnY))
        XCTAssertFalse(region.contains(x: 0.50, y: sideburnY))
        XCTAssertFalse(region.contains(x: 0.02, y: 0.90))
    }

    func testTinyFaceIsDropped() {
        let guide = FaceHairGuide(
            boundingBox: CGRect(x: 0.1, y: 0.1, width: 0.01, height: 0.4),
            hairlineY: nil
        )
        XCTAssertNil(HairRegionBuilder.region(for: guide))
    }

    func testEyebrowHairlineMapsIntoTheFaceBox() {
        let box = CGRect(x: 0.2, y: 0.2, width: 0.4, height: 0.4)
        let hairline = HairFaceGuideBuilder.averageHairlineY(landmarkYs: [0.9, 1.0], box: box)
        XCTAssertEqual(hairline ?? -1, 0.58, accuracy: 0.0001)
        XCTAssertNil(HairFaceGuideBuilder.averageHairlineY(landmarkYs: [], box: box))

        let region = try XCTUnwrap(
            HairRegionBuilder.region(for: FaceHairGuide(boundingBox: box, hairlineY: hairline))
        )
        XCTAssertEqual(region.hairlineY, 0.58, accuracy: 0.0001)
    }

    func testRasterizerKeepsPersonPixelsInsideTheHairWindow() {
        let region = HairRegion(
            window: CGRect(x: 0.2, y: 0.4, width: 0.6, height: 0.5),
            hairlineY: 0.6,
            faceInterior: CGRect(x: 0.35, y: 0.4, width: 0.3, height: 0.2),
            sideburnMinY: 0.45
        )
        let width = 10
        let height = 10
        var person = [UInt8](repeating: 255, count: width * height)
        person[(2 * width) + 4] = 0

        let mask = HairMaskRasterizer.maskBytes(
            person: person,
            width: width,
            height: height,
            regions: [region]
        )

        XCTAssertEqual(mask[(2 * width) + 5], 255)
        XCTAssertEqual(mask[(2 * width) + 4], 0)
        XCTAssertEqual(mask[(5 * width) + 5], 0)
        XCTAssertEqual(mask[(5 * width) + 2], 255)
        XCTAssertEqual(mask[(2 * width) + 0], 0)
    }

    func testRasterizerIsEmptyWithoutAFace() {
        let person = [UInt8](repeating: 255, count: 4)
        let mask = HairMaskRasterizer.maskBytes(person: person, width: 2, height: 2, regions: [])
        XCTAssertEqual(mask, [0, 0, 0, 0])
        XCTAssertEqual(
            HairMaskRasterizer.maskBytes(person: [1], width: 2, height: 2, regions: []),
            []
        )
    }

    func testFrontPortraitBufferIsMirrored() {
        XCTAssertEqual(
            HairColorOrientation.visionOrientation(deviceOrientation: .portrait, cameraPosition: .front),
            .leftMirrored
        )
        XCTAssertEqual(
            HairColorOrientation.visionOrientation(deviceOrientation: .portrait, cameraPosition: .back),
            .right
        )
        XCTAssertEqual(
            HairColorOrientation.captureOrientation(for: .landscapeLeft),
            .landscapeRight
        )
    }

    func testDownscaleCapsTheLongEdge() {
        let image = CIImage(color: .white).cropped(to: CGRect(x: 0, y: 0, width: 2000, height: 1000))
        let small = HairColorOrientation.downscaled(image, maxEdge: 1000)
        XCTAssertEqual(small.extent.width, 1000, accuracy: 0.01)
        XCTAssertEqual(small.extent.height, 500, accuracy: 0.01)
        let unchanged = HairColorOrientation.downscaled(small, maxEdge: 1000)
        XCTAssertEqual(unchanged.extent.width, 1000, accuracy: 0.01)
    }

    func testPhotoOrientationReadsExifIntegers() {
        let key = kCGImagePropertyOrientation as String
        XCTAssertEqual(HairPhotoAlignment.orientation(from: [key: 6]), .right)
        XCTAssertEqual(HairPhotoAlignment.orientation(from: [key: NSNumber(value: 8)]), .left)
        XCTAssertEqual(HairPhotoAlignment.orientation(from: [:]), .up)
    }

    func testMatteTurnsToMatchThePhotoAspect() {
        let wide = CIImage(color: .white).cropped(to: CGRect(x: 0, y: 0, width: 40, height: 20))
        let tall = CIImage(color: .gray).cropped(to: CGRect(x: 0, y: 0, width: 20, height: 40))
        let turned = HairPhotoAlignment.matching(wide, to: tall, orientation: .right)
        XCTAssertEqual(turned.extent.width, 20, accuracy: 0.1)
        XCTAssertEqual(turned.extent.height, 40, accuracy: 0.1)

        let alreadyUpright = HairPhotoAlignment.matching(tall, to: tall, orientation: .right)
        XCTAssertEqual(alreadyUpright.extent.width, 20, accuracy: 0.1)
        XCTAssertEqual(alreadyUpright.extent.height, 40, accuracy: 0.1)
    }

    func testColorBlendTintsOnlyTheMask() throws {
        let size = CGSize(width: 32, height: 16)
        let gray = CIImage(color: CIColor(red: 0.5, green: 0.5, blue: 0.5, alpha: 1))
            .cropped(to: CGRect(origin: .zero, size: size))
        var bytes = [UInt8](repeating: 0, count: Int(size.width * size.height))
        for y in 0..<Int(size.height) {
            for x in 0..<Int(size.width / 2) {
                bytes[(y * Int(size.width)) + x] = 255
            }
        }
        let mask = try XCTUnwrap(HairMaskImage.make(bytes: bytes, width: Int(size.width), height: Int(size.height)))
        let dye = HairDye(id: "red", name: "Red", red: 1, green: 0, blue: 0)
        let context = CIContext(options: [
            .workingColorSpace: CGColorSpaceCreateDeviceRGB(),
            .outputColorSpace: CGColorSpaceCreateDeviceRGB(),
        ])

        let tinted = HairColorCompositor.apply(
            image: gray,
            mask: mask,
            dye: dye,
            strength: 1,
            blurRadius: 0
        )
        let left = try XCTUnwrap(pixel(tinted, x: 4, y: 8, context: context))
        let right = try XCTUnwrap(pixel(tinted, x: 28, y: 8, context: context))
        XCTAssertGreaterThan(left.0, left.1 + 20)
        XCTAssertGreaterThan(left.0, left.2 + 20)
        XCTAssertLessThanOrEqual(abs(right.0 - right.1), 12)
        XCTAssertLessThanOrEqual(abs(right.1 - right.2), 12)
        XCTAssertLessThan(right.0, left.0)

        let untouched = HairColorCompositor.apply(
            image: gray,
            mask: mask,
            dye: dye,
            strength: 0,
            blurRadius: 0
        )
        let plain = try XCTUnwrap(pixel(untouched, x: 4, y: 8, context: context))
        XCTAssertLessThanOrEqual(abs(plain.0 - 128), 12)
        XCTAssertLessThanOrEqual(abs(plain.1 - 128), 12)
        XCTAssertLessThanOrEqual(abs(plain.2 - 128), 12)
    }

    /// Samples one pixel. `x` and `y` are CIImage coordinates, origin bottom-left.
    private func pixel(
        _ image: CIImage,
        x: Int,
        y: Int,
        context: CIContext
    ) -> (Int, Int, Int)? {
        var bytes = [UInt8](repeating: 0, count: 4)
        bytes.withUnsafeMutableBytes { raw in
            guard let base = raw.baseAddress else { return }
            context.render(
                image,
                toBitmap: base,
                rowBytes: 4,
                bounds: CGRect(x: x, y: y, width: 1, height: 1),
                format: .RGBA8,
                colorSpace: CGColorSpaceCreateDeviceRGB()
            )
        }
        return (Int(bytes[0]), Int(bytes[1]), Int(bytes[2]))
    }
}
