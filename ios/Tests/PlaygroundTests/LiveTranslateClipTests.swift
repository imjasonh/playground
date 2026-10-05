import AVFoundation
import CoreImage
import XCTest
@testable import Playground

/// Runs the recorded moving-sign clip through Vision OCR, the Live Translate
/// pipeline, and the follower, with a fake model in place of Foundation Models.
///
/// To change the clip, edit and rerun `ios/scripts/make-live-translate-clip.py`.
final class LiveTranslateClipTests: XCTestCase {
    /// The clip is 24 fps. Every sixth frame is 4 OCR passes per second, about
    /// what the app finishes on a phone.
    private static let frameStride = 6

    private static let fixtures = URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent()
        .appendingPathComponent("Fixtures/LiveTranslate")

    private struct Clip {
        /// Every frame, as the follower sees it.
        var frames: [LiveTranslateGrayFrame] = []
        /// OCR readings of every `frameStride`th frame.
        var passes: [[LiveTranslateObservation]] = []
    }

    func testMovingSignKeepsItsTranslationsOnItsLines() async throws {
        let clip = try await Self.readClip()
        XCTAssertEqual(clip.frames.count, 120)
        XCTAssertEqual(clip.passes.count, 20)
        try XCTSkipIf(clip.passes.allSatisfy(\.isEmpty), "Vision found no text in the clip on this simulator")

        let truth = try LiveTranslateClipTruth.load(from: Self.fixtures.appendingPathComponent("moving-sign.json"))
        let replay = LiveTranslateClipReplay(passes: clip.passes, truth: truth, frameStride: Self.frameStride)
        XCTAssertTrue(
            replay.failures.isEmpty,
            (replay.failures + [replay.transcript]).joined(separator: "\n")
        )

        // Each OCR result lands about when the next pass starts.
        let follow = LiveTranslateFollowReplay(
            frames: clip.frames,
            passes: clip.passes,
            truth: truth,
            frameStride: Self.frameStride,
            latency: Self.frameStride
        )
        XCTAssertTrue(follow.failures.isEmpty, (follow.failures + [follow.summary]).joined(separator: "\n"))
    }

    private static func readClip() async throws -> Clip {
        let asset = AVURLAsset(url: fixtures.appendingPathComponent("moving-sign.mp4"))
        let tracks = try await asset.loadTracks(withMediaType: .video)
        let track = try XCTUnwrap(tracks.first)
        let reader = try AVAssetReader(asset: asset)
        let output = AVAssetReaderTrackOutput(
            track: track,
            outputSettings: [kCVPixelBufferPixelFormatTypeKey as String: kCVPixelFormatType_32BGRA]
        )
        let provider = reader.outputProvider(for: output)
        try reader.start()

        let context = CIContext()
        var clip = Clip()
        var index = 0
        while let sample = try await provider.next() {
            defer { index += 1 }
            guard case .pixelBuffer(let pixels) = sample.content else { continue }
            // The decoder only lends the buffer inside this closure, so copy it
            // out the way the session copies camera frames.
            let rendered = pixels.withUnsafeBuffer { buffer -> CGImage? in
                let frame = CIImage(cvPixelBuffer: buffer)
                return context.createCGImage(frame, from: frame.extent)
            }
            let image = try XCTUnwrap(rendered)
            clip.frames.append(try XCTUnwrap(LiveTranslateGrayFrame(image: image, longSide: 640)))
            if index % frameStride == 0 {
                clip.passes.append(try LiveTranslateRecognizer.recognize(cgImage: image))
            }
        }
        return clip
    }
}
