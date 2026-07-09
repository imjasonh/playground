import XCTest
@testable import Playground

final class MotionAggregatorTests: XCTestCase {
    func testEmptyAggregatorFinishesWithNothing() {
        var agg = MotionAggregator()
        XCTAssertNil(agg.finish())
    }

    func testSamplesWithinOneSecondProduceNoFlushUntilFinish() {
        var agg = MotionAggregator()
        XCTAssertNil(agg.add(t: 0.0, g: 0.2, rotation: 0.1))
        XCTAssertNil(agg.add(t: 0.4, g: 0.6, rotation: 0.3))
        XCTAssertNil(agg.add(t: 0.8, g: 0.4, rotation: 0.2))

        let summary = agg.finish()
        XCTAssertNotNil(summary)
        XCTAssertEqual(summary?.samples, 3)
        XCTAssertEqual(summary?.peakG ?? 0, 0.6, accuracy: 0.0001)
        XCTAssertEqual(summary?.peakRotation ?? 0, 0.3, accuracy: 0.0001)
        XCTAssertEqual(summary?.meanG ?? 0, (0.2 + 0.6 + 0.4) / 3, accuracy: 0.0001)
        XCTAssertEqual(summary?.t ?? -1, 0)
    }

    func testSecondRolloverFlushesPreviousSecond() {
        var agg = MotionAggregator()
        XCTAssertNil(agg.add(t: 0.1, g: 0.5, rotation: 0.0))
        XCTAssertNil(agg.add(t: 0.9, g: 0.9, rotation: 0.0))

        // Crossing into second 1 flushes second 0.
        let flushed = agg.add(t: 1.2, g: 0.1, rotation: 0.0)
        XCTAssertEqual(flushed?.t ?? -1, 0)
        XCTAssertEqual(flushed?.samples, 2)
        XCTAssertEqual(flushed?.peakG ?? 0, 0.9, accuracy: 0.0001)

        let last = agg.finish()
        XCTAssertEqual(last?.t ?? -1, 1)
        XCTAssertEqual(last?.samples, 1)
        XCTAssertEqual(last?.peakG ?? 0, 0.1, accuracy: 0.0001)
    }
}
