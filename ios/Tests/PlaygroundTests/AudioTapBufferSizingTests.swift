import XCTest
@testable import Playground

final class AudioTapBufferSizingTests: XCTestCase {
    func testFrameCountRequestsOneHundredMilliseconds() {
        XCTAssertEqual(AudioTapBufferSizing.frameCount(sampleRate: 16_000), 1_600)
        XCTAssertEqual(AudioTapBufferSizing.frameCount(sampleRate: 44_100), 4_410)
        XCTAssertEqual(AudioTapBufferSizing.frameCount(sampleRate: 48_000), 4_800)
    }

    func testFrameCountFallsBackForInvalidRates() {
        XCTAssertEqual(AudioTapBufferSizing.frameCount(sampleRate: 0), 4_800)
        XCTAssertEqual(AudioTapBufferSizing.frameCount(sampleRate: .nan), 4_800)
    }
}
