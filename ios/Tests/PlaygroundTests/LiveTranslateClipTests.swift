import AVFoundation
import XCTest
@testable import Playground

/// Runs the recorded moving-sign clip through Vision OCR and the Live Translate
/// pipeline, with a fake model in place of Foundation Models.
///
/// To change the clip, edit and rerun `ios/scripts/make-live-translate-clip.py`.
final class LiveTranslateClipTests: XCTestCase {
    /// The clip is 24 fps. Every sixth frame is 4 OCR passes per second, about
    /// what the app finishes on a phone.
    private static let frameStride = 6

    private static let fixtures = URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent()
        .appendingPathComponent("Fixtures/LiveTranslate")

    func testMovingSignKeepsItsTranslations() async throws {
        let passes = try await Self.readClip()
        XCTAssertEqual(passes.count, 20)
        try XCTSkipIf(passes.allSatisfy(\.isEmpty), "Vision found no text in the clip on this simulator")

        let truth = try LiveTranslateClipTruth.load(from: Self.fixtures.appendingPathComponent("moving-sign.json"))
        let replay = LiveTranslateClipReplay(passes: passes, truth: truth, frameStride: Self.frameStride)
        XCTAssertTrue(
            replay.failures.isEmpty,
            (replay.failures + [replay.transcript]).joined(separator: "\n")
        )
    }

    /// OCR readings for every `frameStride`th frame, in order.
    private static func readClip() async throws -> [[LiveTranslateObservation]] {
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

        var passes: [[LiveTranslateObservation]] = []
        var index = 0
        while let sample = try await provider.next() {
            defer { index += 1 }
            guard index % frameStride == 0, case .pixelBuffer(let pixels) = sample.content else { continue }
            // The decoder only lends the buffer inside this closure.
            let readings = pixels.withUnsafeBuffer { buffer in
                Result { try LiveTranslateRecognizer.recognize(pixelBuffer: buffer, orientation: .up) }
            }
            passes.append(try readings.get())
        }
        return passes
    }
}
