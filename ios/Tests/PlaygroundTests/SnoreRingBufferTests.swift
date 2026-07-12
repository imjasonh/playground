import XCTest
@testable import Playground

final class SnoreRingBufferTests: XCTestCase {
    func testRecentSamplesOldestFirstWhenWrapped() {
        var buffer = SnoreRingBuffer(capacity: 4)
        buffer.append([1, 2, 3, 4, 5, 6])
        XCTAssertEqual(buffer.recentSamples(4), [3, 4, 5, 6])
        XCTAssertEqual(buffer.recentSamples(2), [5, 6])
        XCTAssertEqual(buffer.recentSamples(10), [3, 4, 5, 6])
    }

    func testPartialFillReturnsOnlyAvailable() {
        var buffer = SnoreRingBuffer(capacity: 8)
        buffer.append([0.1, 0.2, 0.3])
        XCTAssertEqual(buffer.count, 3)
        XCTAssertEqual(buffer.recentSamples(8), [0.1, 0.2, 0.3])
    }

    func testResetClears() {
        var buffer = SnoreRingBuffer(capacity: 3)
        buffer.append([1, 2, 3])
        buffer.reset()
        XCTAssertEqual(buffer.count, 0)
        XCTAssertEqual(buffer.recentSamples(3), [])
    }
}
