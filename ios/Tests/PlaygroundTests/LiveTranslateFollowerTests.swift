import CoreGraphics
import XCTest
@testable import Playground

final class LiveTranslateFollowerTests: XCTestCase {
    /// Lines of made-up glyphs on a light sign, in scene pixels.
    private static let lines: [(top: Double, height: Double, left: Double, right: Double)] = [
        (80, 14, 40, 160),
        (130, 12, 50, 150),
        (175, 12, 45, 155),
    ]
    private static let width = 200
    private static let height = 300

    /// A frame's camera: scene point `p` lands on pixel `scale * p + (dx, dy)`.
    private struct Camera {
        var scale = 1.0
        var dx = 0.0
        var dy = 0.0

        /// Zoom about the frame center, then pan.
        static func zoom(_ scale: Double, panX: Double = 0, panY: Double = 0) -> Camera {
            Camera(
                scale: scale,
                dx: Double(width) / 2 * (1 - scale) + panX,
                dy: Double(height) / 2 * (1 - scale) + panY
            )
        }
    }

    func testFollowsAPan() throws {
        let cameras = (0...10).map { Camera(dx: 3 * Double($0), dy: 1.5 * Double($0)) }
        var follower = start(with: cameras[0])
        for number in 1...10 {
            follower.advance(to: Self.render(cameras[number]), number: number)
            try assertPositions(follower, match: cameras[number], tolerance: 0.5)
        }
    }

    func testFollowsAZoom() throws {
        let cameras = (0...10).map { Camera.zoom(1 + 0.012 * Double($0), panX: Double($0)) }
        var follower = start(with: cameras[0])
        for number in 1...10 {
            follower.advance(to: Self.render(cameras[number]), number: number)
            try assertPositions(follower, match: cameras[number], tolerance: 1, sizeTolerance: 0.03)
        }
    }

    func testPlacesALateOCRResultWhereItsLinesAreNow() throws {
        let cameras = (0...8).map { Camera(dx: -4 * Double($0), dy: 2 * Double($0)) }
        var follower = start(with: cameras[0])
        for number in 1...8 {
            let frame = Self.render(cameras[number])
            follower.advance(to: frame, number: number)
            if number == 3 {
                follower.hold(frame, for: number)
            }
        }
        // The pass that read frame 3 finishes while frame 8 is on screen, and it
        // no longer sees the last line.
        let boxes = Self.boxes(cameras[3]).filter { $0.key != "line-2" }
        follower.rebase(boxes, from: 3)
        XCTAssertEqual(Set(follower.positions.keys), ["line-0", "line-1"])
        try assertPositions(follower, match: cameras[8], tolerance: 0.5)
    }

    func testMovesAHiddenLineWithTheOthers() throws {
        let cameras = (0...8).map { Camera(dx: 2.5 * Double($0), dy: -2 * Double($0)) }
        var follower = start(with: cameras[0])
        for number in 1...8 {
            // Glare washes out the middle line from frame 3 on.
            follower.advance(to: Self.render(cameras[number], hiding: number >= 3 ? 1 : nil), number: number)
        }
        try assertPositions(follower, match: cameras[8], tolerance: 1)
    }

    func testKeepsItsSharpPatchesWhenOCRReadABlurredFrame() throws {
        let cameras = (0...10).map { Camera(dx: 2 * Double($0), dy: Double($0)) }
        var follower = start(with: cameras[0])
        for number in 1...10 {
            // Shake smears frame 4 while OCR reads it.
            let frame = Self.render(cameras[number], blur: number == 4 ? 12 : 0)
            follower.advance(to: frame, number: number)
            if number == 4 {
                follower.hold(frame, for: number)
            }
        }
        // OCR's boxes for a smeared frame land a few pixels off.
        let smeared = Self.boxes(cameras[4]).mapValues { $0.offsetBy(dx: 0, dy: 3 / Double(Self.height)) }
        follower.rebase(smeared, from: 4)
        try assertPositions(follower, match: cameras[10], tolerance: 0.5)
    }

    func testForgetsEverythingOnReset() {
        var follower = start(with: Camera())
        follower.reset()
        XCTAssertTrue(follower.positions.isEmpty)
    }

    // MARK: - Helpers

    private func start(with camera: Camera) -> LiveTranslateFollower {
        var follower = LiveTranslateFollower()
        let frame = Self.render(camera)
        follower.advance(to: frame, number: 0)
        follower.hold(frame, for: 0)
        follower.rebase(Self.boxes(camera), from: 0)
        return follower
    }

    private func assertPositions(
        _ follower: LiveTranslateFollower,
        match camera: Camera,
        tolerance: CGFloat,
        sizeTolerance: CGFloat = 0.02,
        file: StaticString = #filePath,
        line: UInt = #line
    ) throws {
        let truth = Self.boxes(camera)
        for (id, shown) in follower.positions {
            let actual = try XCTUnwrap(truth[id], file: file, line: line)
            let width = CGFloat(Self.width)
            let height = CGFloat(Self.height)
            XCTAssertEqual(shown.midX * width, actual.midX * width, accuracy: tolerance, id, file: file, line: line)
            XCTAssertEqual(shown.midY * height, actual.midY * height, accuracy: tolerance, id, file: file, line: line)
            XCTAssertEqual(shown.height / actual.height, 1, accuracy: sizeTolerance, id, file: file, line: line)
        }
    }

    /// Each line's Vision-normalized box as `camera` sees it, by track id.
    private static func boxes(_ camera: Camera) -> [String: CGRect] {
        var result: [String: CGRect] = [:]
        for (index, line) in lines.enumerated() {
            let left = camera.scale * line.left + camera.dx
            let top = camera.scale * line.top + camera.dy
            let right = camera.scale * line.right + camera.dx
            let bottom = camera.scale * (line.top + line.height) + camera.dy
            result["line-\(index)"] = CGRect(
                x: left / Double(width),
                y: 1 - bottom / Double(height),
                width: (right - left) / Double(width),
                height: (bottom - top) / Double(height)
            )
        }
        return result
    }

    /// `blur` smears the frame across that many pixels sideways, like a fast pan.
    private static func render(_ camera: Camera, hiding hidden: Int? = nil, blur: Double = 0) -> LiveTranslateGrayFrame {
        let taps = blur > 0 ? 9 : 1
        var pixels = [UInt8](repeating: 0, count: width * height)
        for row in 0..<height {
            for column in 0..<width {
                var total = 0.0
                for tap in 0..<taps {
                    let smear = taps == 1 ? 0 : blur * (Double(tap) / Double(taps - 1) - 0.5)
                    for sub in 0..<4 {
                        let x = (Double(column) + 0.25 + 0.5 * Double(sub % 2) - camera.dx - smear) / camera.scale
                        let y = (Double(row) + 0.25 + 0.5 * Double(sub / 2) - camera.dy) / camera.scale
                        total += brightness(x, y, hiding: hidden)
                    }
                }
                pixels[row * width + column] = UInt8(total / Double(4 * taps))
            }
        }
        return LiveTranslateGrayFrame(width: width, height: height, pixels: pixels)
    }

    private static func brightness(_ x: Double, _ y: Double, hiding hidden: Int?) -> Double {
        let paper = 205 + 12 * sin(x / 37) * cos(y / 53)
        for (index, line) in lines.enumerated()
        where y >= line.top && y < line.top + line.height && x >= line.left && x < line.right {
            if index == hidden {
                return 240
            }
            let glyph = Int((x - line.left) / 7)
            let seed = (glyph * 7919 + index * 104_729) % 97
            guard seed % 6 != 0 else { return paper }
            let local = x - line.left - Double(glyph) * 7
            let stem = Double(seed % 4) + 1
            let across = (y - line.top) / line.height
            let inked = abs(local - stem) < 0.9
                || abs(local - stem - 3) < 0.7 && seed % 3 != 0
                || abs(across - Double(seed % 3 + 1) * 0.25) < 0.1 && local < 6
            return inked ? 40 : paper
        }
        return paper
    }
}
