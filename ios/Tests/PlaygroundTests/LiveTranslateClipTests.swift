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

    func testMovingSignKeepsItsTranslations() async throws {
        let passes = try await Self.readClip()
        XCTAssertEqual(passes.count, 20)
        try XCTSkipIf(passes.allSatisfy(\.isEmpty), "Vision found no text in the clip on this simulator")

        let replay = LiveTranslateClipReplay(passes: passes)
        XCTAssertTrue(
            replay.failures.isEmpty,
            (replay.failures + [replay.transcript]).joined(separator: "\n")
        )
    }

    /// OCR readings for every `frameStride`th frame, in order.
    private static func readClip() async throws -> [[LiveTranslateObservation]] {
        let url = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .appendingPathComponent("Fixtures/LiveTranslate/moving-sign.mp4")
        let asset = AVURLAsset(url: url)
        let tracks = try await asset.loadTracks(withMediaType: .video)
        let track = try XCTUnwrap(tracks.first)
        let reader = try AVAssetReader(asset: asset)
        let output = AVAssetReaderTrackOutput(
            track: track,
            outputSettings: [kCVPixelBufferPixelFormatTypeKey as String: kCVPixelFormatType_32BGRA]
        )
        reader.add(output)
        guard reader.startReading() else {
            throw reader.error ?? CocoaError(.fileReadCorruptFile)
        }

        var passes: [[LiveTranslateObservation]] = []
        var index = 0
        while let sample = output.copyNextSampleBuffer() {
            defer { index += 1 }
            guard index % frameStride == 0, let pixels = CMSampleBufferGetImageBuffer(sample) else { continue }
            passes.append(try LiveTranslateRecognizer.recognize(pixelBuffer: pixels, orientation: .up))
        }
        if let error = reader.error {
            throw error
        }
        return passes
    }
}
