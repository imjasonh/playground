import XCTest
@testable import Playground

final class ZDepthBandTests: XCTestCase {
    func testOpenBandKeepsFiniteDepths() {
        let band = ZDepthBand.open
        XCTAssertTrue(band.contains(0))
        XCTAssertTrue(band.contains(0.4))
        XCTAssertTrue(band.contains(12))
        XCTAssertFalse(band.contains(-1))
        XCTAssertFalse(band.contains(.nan))
        XCTAssertFalse(band.contains(.infinity))
    }

    func testThresholdBand() {
        let band = ZDepthBand(near: .meters(0.5), far: .meters(1.5))
        XCTAssertFalse(band.contains(0.49))
        XCTAssertTrue(band.contains(0.5))
        XCTAssertTrue(band.contains(1.0))
        XCTAssertTrue(band.contains(1.5))
        XCTAssertFalse(band.contains(1.51))
    }

    func testNearZeroFarInfinity() {
        let band = ZDepthBand(near: .meters(0), far: .infinity)
        XCTAssertTrue(band.contains(0.01))
        XCTAssertTrue(band.contains(100))
    }

    func testNearInfinityShowsNothingFinite() {
        let band = ZDepthBand(near: .infinity, far: .infinity)
        XCTAssertFalse(band.contains(0))
        XCTAssertFalse(band.contains(3))
    }

    func testClampOrdersBounds() {
        let inverted = ZDepthBand(near: .meters(3), far: .meters(1)).clamped()
        XCTAssertEqual(inverted.near, .meters(1))
        XCTAssertEqual(inverted.far, .meters(1))
    }

    func testSliderMappingInfinityAtTop() {
        XCTAssertEqual(ZDepthSliderMapping.bound(sliderValue: 0), .meters(0))
        XCTAssertEqual(ZDepthSliderMapping.bound(sliderValue: 0.5), .meters(2.5))
        XCTAssertEqual(ZDepthSliderMapping.bound(sliderValue: 1), .infinity)
        XCTAssertEqual(ZDepthSliderMapping.sliderValue(for: .infinity), 1, accuracy: 0.0001)
        XCTAssertEqual(
            ZDepthSliderMapping.sliderValue(for: .meters(2.5)),
            0.5,
            accuracy: 0.0001
        )
    }

    func testBoundLabels() {
        XCTAssertEqual(ZDepthBand.Bound.label(.infinity), "∞")
        XCTAssertEqual(ZDepthBand.Bound.label(.meters(0)), "0 m")
        XCTAssertEqual(ZDepthBand.Bound.label(.meters(0.4)), "40 cm")
        XCTAssertEqual(ZDepthBand.Bound.label(.meters(2.25)), "2.25 m")
    }
}

final class ZDepthBandMaskerTests: XCTestCase {
    func testMaskBlacksOutOutsideBand() {
        // 2×1 BGRA image, white pixels.
        var bgra: [UInt8] = [
            255, 255, 255, 255,
            255, 255, 255, 255,
        ]
        // Matching 2×1 depth map: 0.3 m and 2.0 m.
        let depth: [Float] = [0.3, 2.0]
        let band = ZDepthBand(near: .meters(0.5), far: .meters(1.5))

        ZDepthBandMasker.applyBand(
            bgra: &bgra,
            width: 2,
            height: 1,
            depth: depth,
            depthWidth: 2,
            depthHeight: 1,
            band: band
        )

        // First pixel (0.3 m) outside → black.
        XCTAssertEqual(Array(bgra[0..<4]), [0, 0, 0, 255])
        // Second pixel (2.0 m) outside → black.
        XCTAssertEqual(Array(bgra[4..<8]), [0, 0, 0, 255])
    }

    func testMaskKeepsInsideBand() {
        var bgra: [UInt8] = [
            10, 20, 30, 255,
            40, 50, 60, 255,
        ]
        let depth: [Float] = [0.8, 1.2]
        let band = ZDepthBand(near: .meters(0.5), far: .meters(1.5))

        ZDepthBandMasker.applyBand(
            bgra: &bgra,
            width: 2,
            height: 1,
            depth: depth,
            depthWidth: 2,
            depthHeight: 1,
            band: band
        )

        XCTAssertEqual(Array(bgra[0..<4]), [10, 20, 30, 255])
        XCTAssertEqual(Array(bgra[4..<8]), [40, 50, 60, 255])
    }

    func testInvalidDepthBecomesBlack() {
        var bgra: [UInt8] = [9, 9, 9, 255]
        let depth: [Float] = [Float.nan]
        let band = ZDepthBand.open

        ZDepthBandMasker.applyBand(
            bgra: &bgra,
            width: 1,
            height: 1,
            depth: depth,
            depthWidth: 1,
            depthHeight: 1,
            band: band
        )

        XCTAssertEqual(bgra, [0, 0, 0, 255])
    }

    func testMirrorSamplesOppositeDepthColumn() {
        var bgra: [UInt8] = [
            255, 255, 255, 255, // will sample depth column 1 when mirrored
            255, 255, 255, 255, // will sample depth column 0 when mirrored
        ]
        // Only the left depth sample is inside the band.
        let depth: [Float] = [1.0, 3.0]
        let band = ZDepthBand(near: .meters(0.5), far: .meters(1.5))

        ZDepthBandMasker.applyBand(
            bgra: &bgra,
            width: 2,
            height: 1,
            depth: depth,
            depthWidth: 2,
            depthHeight: 1,
            band: band,
            mirrorX: true
        )

        // x=0 mirrors to depth 3.0 → black; x=1 mirrors to depth 1.0 → kept white.
        XCTAssertEqual(Array(bgra[0..<4]), [0, 0, 0, 255])
        XCTAssertEqual(Array(bgra[4..<8]), [255, 255, 255, 255])
    }

    func testOverlayToneQuantizesIntoBands() {
        let near = 0.0
        let far = 5.0
        let first = ZDepthBandMasker.overlayTone(depthMeters: 0.1, near: near, far: far)
        let mid = ZDepthBandMasker.overlayTone(depthMeters: 2.5, near: near, far: far)
        let last = ZDepthBandMasker.overlayTone(depthMeters: 4.9, near: near, far: far)
        XCTAssertEqual(first, 0, accuracy: 0.001)
        XCTAssertGreaterThan(mid, first)
        XCTAssertEqual(last, 1, accuracy: 0.001)
        // Adjacent depths in the same step share a tone.
        let a = ZDepthBandMasker.overlayTone(depthMeters: 0.05, near: near, far: far)
        let b = ZDepthBandMasker.overlayTone(depthMeters: 0.2, near: near, far: far)
        XCTAssertEqual(a, b, accuracy: 0.001)
    }

    func testOverlayBlueGetsDarkerWithTone() {
        let near = ZDepthBandMasker.overlayBlueBGRA(tone: 0)
        let far = ZDepthBandMasker.overlayBlueBGRA(tone: 1)
        // Near is lighter (higher R/G); far is darker navy (lower R/G, still blue-heavy).
        XCTAssertGreaterThan(near.r, far.r)
        XCTAssertGreaterThan(near.g, far.g)
        XCTAssertGreaterThan(near.b, far.r)
        XCTAssertGreaterThan(far.b, far.r)
    }

    func testDepthOverlayTintsKeptPixels() {
        var bgra: [UInt8] = [
            200, 200, 200, 255, // near depth
            200, 200, 200, 255, // far depth
        ]
        let depth: [Float] = [0.6, 1.4]
        let band = ZDepthBand(near: .meters(0.5), far: .meters(1.5))

        ZDepthBandMasker.applyBand(
            bgra: &bgra,
            width: 2,
            height: 1,
            depth: depth,
            depthWidth: 2,
            depthHeight: 1,
            band: band,
            overlayDepth: true
        )

        // Both stay non-black (inside band) and are tinted differently.
        XCTAssertNotEqual(Array(bgra[0..<3]), [0, 0, 0])
        XCTAssertNotEqual(Array(bgra[4..<7]), [0, 0, 0])
        XCTAssertNotEqual(Array(bgra[0..<3]), Array(bgra[4..<7]))
        // Near pixel should be lighter overall than far pixel.
        let nearLuma = Int(bgra[0]) + Int(bgra[1]) + Int(bgra[2])
        let farLuma = Int(bgra[4]) + Int(bgra[5]) + Int(bgra[6])
        XCTAssertGreaterThan(nearLuma, farLuma)
    }
}
