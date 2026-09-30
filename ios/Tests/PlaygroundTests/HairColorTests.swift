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

    func testForeheadStaysOutsideTheProtectedFace() throws {
        let box = CGRect(x: 0.30, y: 0.40, width: 0.40, height: 0.28)
        let region = try XCTUnwrap(
            HairRegionBuilder.region(for: FaceHairGuide(boundingBox: box, eyebrowY: 0.58))
        )
        XCTAssertTrue(region.crown.contains(CGPoint(x: 0.50, y: 0.80)))
        XCTAssertFalse(region.protected.contains(CGPoint(x: 0.50, y: 0.63)))
        XCTAssertTrue(region.protected.contains(CGPoint(x: 0.50, y: 0.48)))
        XCTAssertTrue(region.search.contains(CGPoint(x: 0.20, y: 0.15)))
        XCTAssertNil(
            HairRegionBuilder.region(
                for: FaceHairGuide(boundingBox: CGRect(x: 0.1, y: 0.1, width: 0.01, height: 0.4), eyebrowY: nil)
            )
        )
    }

    func testEyebrowLineMapsIntoTheFaceBox() {
        let box = CGRect(x: 0.2, y: 0.2, width: 0.4, height: 0.4)
        let eyebrow = HairFaceGuideBuilder.averageEyebrowY(landmarkYs: [0.55, 0.65], box: box)
        XCTAssertEqual(eyebrow ?? -1, 0.44, accuracy: 0.0001)
        XCTAssertNil(HairFaceGuideBuilder.averageEyebrowY(landmarkYs: [], box: box))
    }

    func testBareForeheadIsNotDyed() throws {
        let (colors, person) = try portrait(bangs: false, longHair: false, shirtMatchesHair: false)
        let mask = try affinityMask(colors: colors, person: person)
        XCTAssertEqual(mask[index(x: 20, y: 4)], 255)
        XCTAssertEqual(mask[index(x: 20, y: 18)], 0)
        XCTAssertEqual(mask[index(x: 20, y: 24)], 0)
        XCTAssertEqual(mask[index(x: 20, y: 42)], 0)
    }

    func testBangsAndLongHairAreDyed() throws {
        let (colors, person) = try portrait(bangs: true, longHair: true, shirtMatchesHair: false)
        let mask = try affinityMask(colors: colors, person: person)
        XCTAssertEqual(mask[index(x: 20, y: 4)], 255)
        XCTAssertEqual(mask[index(x: 20, y: 18)], 255)
        XCTAssertEqual(mask[index(x: 20, y: 24)], 0)
        XCTAssertEqual(mask[index(x: 8, y: 35)], 255)
        XCTAssertEqual(mask[index(x: 20, y: 32)], 0)
        XCTAssertEqual(mask[index(x: 20, y: 42)], 0)
    }

    func testHairColoredBeardStaysOut() throws {
        var (colors, person) = try portrait(bangs: false, longHair: true, shirtMatchesHair: false)
        // Beard matches the crown, and still sits inside the protected face.
        fill(&colors, person: &person, x0: 0.36, y0: 0.40, x1: 0.64, y1: 0.50, color: hairColor)
        let mask = try affinityMask(colors: colors, person: person)
        XCTAssertEqual(mask[index(x: 20, y: 27)], 0)
        XCTAssertEqual(mask[index(x: 8, y: 20)], 255)
    }

    func testBaldHeadIsNotDyed() throws {
        let width = 40
        let height = 50
        var colors = [HairRGB](repeating: background, count: width * height)
        var person = [UInt8](repeating: 0, count: width * height)
        fill(&colors, person: &person, x0: 0.22, y0: 0.05, x1: 0.78, y1: 0.95, color: skinColor, value: 255)
        let mask = try affinityMask(colors: colors, person: person)
        XCTAssertFalse(mask.contains { $0 > 0 })
    }

    func testSameColorClothesTouchingTheHairAreDyed() throws {
        let (colors, person) = try portrait(bangs: false, longHair: true, shirtMatchesHair: true)
        let mask = try affinityMask(colors: colors, person: person)
        XCTAssertEqual(mask[index(x: 20, y: 18)], 0)
        XCTAssertEqual(mask[index(x: 20, y: 44)], 255)
    }

    func testAffinityMaskRejectsAMismatchedBuffer() {
        let colors = [HairRGB](repeating: skinColor, count: 4)
        XCTAssertEqual(
            HairAffinity.maskBytes(colors: colors, person: [255], width: 2, height: 2, regions: []),
            []
        )
        XCTAssertEqual(
            HairAffinity.maskBytes(colors: colors, person: [UInt8](repeating: 255, count: 4), width: 2, height: 2, regions: []),
            [0, 0, 0, 0]
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
        XCTAssertEqual(HairColorOrientation.photoRotationAngle(for: .portrait), 90)
        XCTAssertEqual(HairColorOrientation.photoRotationAngle(for: .portraitUpsideDown), 270)
        XCTAssertEqual(HairColorOrientation.photoRotationAngle(for: .landscapeLeft), 0)
        XCTAssertEqual(HairColorOrientation.photoRotationAngle(for: .landscapeRight), 180)
        XCTAssertEqual(HairColorOrientation.photoRotationAngle(for: .faceUp), 90)
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

    func testSamplerRowZeroIsTheTopOfTheImage() throws {
        let width = 8
        let height = 8
        guard let bitmap = CGContext(
            data: nil,
            width: width,
            height: height,
            bitsPerComponent: 8,
            bytesPerRow: 0,
            space: CGColorSpaceCreateDeviceRGB(),
            bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
        ) else {
            XCTFail("Could not make a bitmap")
            return
        }
        bitmap.setFillColor(CGColor(srgbRed: 0, green: 0, blue: 1, alpha: 1))
        bitmap.fill(CGRect(x: 0, y: 0, width: width, height: height))
        bitmap.setFillColor(CGColor(srgbRed: 1, green: 0, blue: 0, alpha: 1))
        bitmap.fill(CGRect(x: 0, y: 4, width: width, height: 4))
        let rendered = try XCTUnwrap(bitmap.makeImage())
        let image = CIImage(cgImage: rendered)
        let colors = try XCTUnwrap(HairImageSampler.colors(from: image, width: width, height: height))
        let context = CIContext(options: [
            .workingColorSpace: CGColorSpaceCreateDeviceRGB(),
            .outputColorSpace: CGColorSpaceCreateDeviceRGB(),
        ])
        let top = try XCTUnwrap(pixel(image, x: 1, y: 6, context: context))
        let bottom = try XCTUnwrap(pixel(image, x: 1, y: 1, context: context))
        XCTAssertGreaterThan(top.0, 200)
        XCTAssertLessThan(top.2, 40)
        XCTAssertGreaterThan(bottom.2, 200)
        XCTAssertLessThanOrEqual(abs(Int((colors[0].r * 255).rounded()) - top.0), 2)
        XCTAssertLessThanOrEqual(abs(Int((colors[(7 * width)].b * 255).rounded()) - bottom.2), 2)
    }

    private let skinColor = HairRGB(r: 0.82, g: 0.63, b: 0.51)
    private let hairColor = HairRGB(r: 0.16, g: 0.09, b: 0.06)
    private let shirtColor = HairRGB(r: 0.15, g: 0.25, b: 0.55)
    private let background = HairRGB(r: 0.20, g: 0.55, b: 0.20)
    private let portraitWidth = 40
    private let portraitHeight = 50

    private func portrait(
        bangs: Bool,
        longHair: Bool,
        shirtMatchesHair: Bool
    ) throws -> ([HairRGB], [UInt8]) {
        let width = portraitWidth
        let height = portraitHeight
        var colors = [HairRGB](repeating: background, count: width * height)
        var person = [UInt8](repeating: 0, count: width * height)
        fill(&colors, person: &person, x0: 0.22, y0: 0.05, x1: 0.78, y1: 0.95, color: skinColor, value: 255)
        fill(&colors, person: &person, x0: 0.18, y0: 0.68, x1: 0.82, y1: 0.95, color: hairColor, value: 255)
        let shirt = shirtMatchesHair ? hairColor : shirtColor
        let shirtTop: CGFloat = shirtMatchesHair ? 0.32 : 0.28
        fill(&colors, person: &person, x0: 0.32, y0: 0.05, x1: 0.68, y1: shirtTop, color: shirt, value: 255)
        if bangs {
            fill(&colors, person: &person, x0: 0.32, y0: 0.58, x1: 0.68, y1: 0.68, color: hairColor, value: 255)
        }
        if longHair {
            fill(&colors, person: &person, x0: 0.12, y0: 0.05, x1: 0.28, y1: 0.95, color: hairColor, value: 255)
            fill(&colors, person: &person, x0: 0.72, y0: 0.05, x1: 0.88, y1: 0.95, color: hairColor, value: 255)
        }
        if shirtMatchesHair {
            fill(&colors, person: &person, x0: 0.28, y0: 0.02, x1: 0.72, y1: 0.32, color: hairColor, value: 255)
        }
        return (colors, person)
    }

    private func affinityMask(colors: [HairRGB], person: [UInt8]) throws -> [UInt8] {
        let region = try XCTUnwrap(
            HairRegionBuilder.region(
                for: FaceHairGuide(
                    boundingBox: CGRect(x: 0.30, y: 0.40, width: 0.40, height: 0.28),
                    eyebrowY: 0.58
                )
            )
        )
        return HairAffinity.maskBytes(
            colors: colors,
            person: person,
            width: portraitWidth,
            height: portraitHeight,
            regions: [region]
        )
    }

    private func index(x: Int, y: Int) -> Int {
        (y * portraitWidth) + x
    }

    private func fill(
        _ colors: inout [HairRGB],
        person: inout [UInt8],
        x0: CGFloat,
        y0: CGFloat,
        x1: CGFloat,
        y1: CGFloat,
        color: HairRGB,
        value: UInt8 = 255
    ) {
        for y in 0..<portraitHeight {
            for x in 0..<portraitWidth {
                let nx = (CGFloat(x) + 0.5) / CGFloat(portraitWidth)
                let ny = 1 - ((CGFloat(y) + 0.5) / CGFloat(portraitHeight))
                guard nx >= x0, nx <= x1, ny >= y0, ny <= y1 else { continue }
                let slot = (y * portraitWidth) + x
                colors[slot] = color
                person[slot] = value
            }
        }
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
