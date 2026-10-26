import XCTest
@testable import Roll

final class MonitorPhotoTests: XCTestCase {
    private func flat(_ value: UInt8, width: Int = 120, height: Int = 80) -> RGBAImage {
        var pixels = [UInt8](repeating: value, count: width * height * 4)
        for index in stride(from: 3, to: pixels.count, by: 4) {
            pixels[index] = 255
        }
        return RGBAImage(width: width, height: height, pixels: pixels)
    }

    private func meanLevel(_ image: RGBAImage) -> Double {
        var sum = 0
        for (index, value) in image.pixels.enumerated() where index % 4 != 3 {
            sum += Int(value)
        }
        return Double(sum) / Double(image.width * image.height * 3)
    }

    func testStyleRepeatsForSeed() {
        XCTAssertEqual(MonitorPhotoStyle.random(seed: 7), MonitorPhotoStyle.random(seed: 7))
        XCTAssertNotEqual(MonitorPhotoStyle.random(seed: 7), MonitorPhotoStyle.random(seed: 8))
    }

    func testStyleKeepsWhiteBelowClipping() {
        for seed in 0..<200 {
            let style = MonitorPhotoStyle.random(seed: UInt64(seed))
            XCTAssertLessThanOrEqual(style.whiteBalance.max(), 1, "seed \(seed)")
            XCTAssertLessThan(style.exposure, 1, "seed \(seed)")
            XCTAssertGreaterThan(style.zoom, 1, "seed \(seed)")
        }
    }

    func testFilterIsDeterministicAndKeepsSize() {
        let input = flat(128)
        let style = MonitorPhotoStyle.random(seed: 42)
        let first = MonitorPhotoFilter.apply(input, style: style)
        let second = MonitorPhotoFilter.apply(input, style: style)
        XCTAssertEqual(first, second)
        XCTAssertEqual(first.width, input.width)
        XCTAssertEqual(first.height, input.height)
    }

    func testOutputIsOpaque() {
        let output = MonitorPhotoFilter.apply(flat(200), style: .random(seed: 3))
        for index in stride(from: 3, to: output.pixels.count, by: 4) {
            XCTAssertEqual(output.pixels[index], 255)
        }
    }

    func testBlackScreenPhotographsAsDarkGray() {
        for seed in 0..<5 {
            let output = MonitorPhotoFilter.apply(flat(0), style: .random(seed: UInt64(seed)))
            XCTAssertGreaterThan(meanLevel(output), 8, "seed \(seed)")
        }
    }

    func testWhiteScreenPhotographsBelowWhite() {
        for seed in 0..<5 {
            let output = MonitorPhotoFilter.apply(flat(255), style: .random(seed: UInt64(seed)))
            XCTAssertLessThan(meanLevel(output), 245, "seed \(seed)")
        }
    }

    func testFlatScreenGetsTexture() {
        let output = MonitorPhotoFilter.apply(flat(180), style: .random(seed: 9))
        XCTAssertGreaterThan(Set(output.pixels).count, 20)
    }

    func testBoxBlurKeepsFlatPlane() {
        let plane = [Float](repeating: 0.25, count: 30 * 20)
        let blurred = MonitorPhotoFilter.boxBlur(plane, width: 30, height: 20, radius: 3)
        for value in blurred {
            XCTAssertEqual(value, 0.25, accuracy: 1e-5)
        }
    }

    func testBoxBlurSpreadsAPoint() {
        var plane = [Float](repeating: 0, count: 9 * 9)
        plane[4 * 9 + 4] = 9
        let blurred = MonitorPhotoFilter.boxBlur(plane, width: 9, height: 9, radius: 1)
        XCTAssertEqual(blurred[4 * 9 + 4], 1, accuracy: 1e-5)
        XCTAssertEqual(blurred[3 * 9 + 3], 1, accuracy: 1e-5)
        XCTAssertEqual(blurred[2 * 9 + 2], 0, accuracy: 1e-5)
    }
}
