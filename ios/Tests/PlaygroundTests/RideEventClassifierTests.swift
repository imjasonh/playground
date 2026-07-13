import XCTest
@testable import Playground

final class RideEventClassifierTests: XCTestCase {
    private let hz = 50.0

    /// Feed a constant magnitude for `duration` seconds, collecting all events.
    private func feed(
        _ classifier: inout RideEventClassifier,
        magnitude: Double,
        duration: TimeInterval,
        startAt: TimeInterval
    ) -> (events: [RideEvent], endTime: TimeInterval) {
        var events: [RideEvent] = []
        let dt = 1.0 / hz
        var t = startAt
        let end = startAt + duration
        while t < end {
            events += classifier.process(magnitude: magnitude, at: t)
            t += dt
        }
        return (events, t)
    }

    func testCalmRideProducesNoEvents() {
        var c = RideEventClassifier()
        let (events, _) = feed(&c, magnitude: 0.05, duration: 5, startAt: 0)
        XCTAssertTrue(events.isEmpty)
    }

    func testRoadBuzzIsIgnored() {
        var c = RideEventClassifier()
        // Typical bike vibration sits well under the 1.5g recording floor.
        let (events, _) = feed(&c, magnitude: 0.75, duration: 3, startAt: 0)
        XCTAssertTrue(events.isEmpty)
    }

    func testShakeBelowPotholeFloorIsNotRecorded() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        all += feed(&c, magnitude: 1.2, duration: 0.1, startAt: 1).events   // old shake range
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 1.1).events
        XCTAssertTrue(all.isEmpty, "sub-pothole jolts must not produce events")
    }

    func testPotholeIsClassifiedAsPothole() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        all += feed(&c, magnitude: 1.6, duration: 0.1, startAt: 1).events
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 1.1).events
        XCTAssertEqual(all.map(\.severity), [.pothole])
        XCTAssertGreaterThanOrEqual(all.first?.peakG ?? 0, 1.5)
    }

    func testHardImpactBelowCrashThresholdDoesNotBecomeCrash() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        all += feed(&c, magnitude: 3.7, duration: 0.1, startAt: 1).events   // impact but < crashImpact 4.0
        all += feed(&c, magnitude: 0.02, duration: 5, startAt: 1.1).events  // long stillness
        XCTAssertEqual(all.map(\.severity), [.impact])
        XCTAssertFalse(all.contains { $0.severity == .crash })
    }

    func testCrashIsImpactFollowedByStillness() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.3, duration: 2, startAt: 0).events     // riding
        all += feed(&c, magnitude: 5.0, duration: 0.1, startAt: 2).events   // big impact
        all += feed(&c, magnitude: 0.02, duration: 4, startAt: 2.1).events  // still for > 3s
        let severities = all.map(\.severity)
        XCTAssertTrue(severities.contains(.impact))
        XCTAssertTrue(severities.contains(.crash))
    }

    func testImpactThenResumedMotionIsNotCrash() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.3, duration: 2, startAt: 0).events
        all += feed(&c, magnitude: 5.0, duration: 0.1, startAt: 2).events   // big impact
        all += feed(&c, magnitude: 0.02, duration: 1, startAt: 2.1).events  // brief stillness (< 3s)
        all += feed(&c, magnitude: 0.4, duration: 3, startAt: 3.1).events   // rider keeps going
        XCTAssertTrue(all.contains { $0.severity == .impact })
        XCTAssertFalse(all.contains { $0.severity == .crash })
    }

    func testDebounceCollapsesRingingIntoOneEvent() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        // Two spikes 0.1s apart — within the 0.8s debounce → one event.
        all += feed(&c, magnitude: 1.8, duration: 0.06, startAt: 1.0).events
        all += feed(&c, magnitude: 0.05, duration: 0.1, startAt: 1.06).events
        all += feed(&c, magnitude: 1.8, duration: 0.06, startAt: 1.16).events
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 1.22).events
        XCTAssertEqual(all.count, 1)
    }

    func testSeparateBumpsBeyondDebounceAreDistinctEvents() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        all += feed(&c, magnitude: 1.8, duration: 0.06, startAt: 1.0).events
        all += feed(&c, magnitude: 0.05, duration: 1.0, startAt: 1.06).events   // well beyond debounce
        all += feed(&c, magnitude: 1.8, duration: 0.06, startAt: 2.1).events
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 2.16).events
        XCTAssertEqual(all.count, 2)
    }

    func testFlushOpenBurstAfterSensingGapEmitsPreGapImpact() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        // Burst starts but never falls below the floor — then sensing dies (suspend).
        all += feed(&c, magnitude: 5.85, duration: 0.2, startAt: 1.0).events
        XCTAssertTrue(all.isEmpty, "burst still open while magnitude stays high")

        let flushed = c.flushOpenBurst(endingAt: 1.2)
        XCTAssertEqual(flushed.count, 1)
        XCTAssertEqual(flushed.first?.severity, .impact)
        XCTAssertEqual(flushed.first?.peakG ?? 0, 5.85, accuracy: 0.0001)
        XCTAssertEqual(flushed.first?.at ?? -1, 1.0, accuracy: 0.05)
    }

    func testFlushOpenBurstClearsCrashWatch() {
        var c = RideEventClassifier()
        _ = feed(&c, magnitude: 5.0, duration: 0.1, startAt: 0).events
        // Burst ends → crash armed; then a long suspend before stillness completes.
        _ = feed(&c, magnitude: 0.02, duration: 0.5, startAt: 0.1).events
        _ = c.flushOpenBurst(endingAt: 0.6)

        // After flush, continued stillness must not emit a crash.
        let (after, _) = feed(&c, magnitude: 0.02, duration: 5, startAt: 100)
        XCTAssertFalse(after.contains { $0.severity == .crash })
    }

    func testProcessAutoFlushesAcrossSampleGap() {
        var c = RideEventClassifier()
        _ = feed(&c, magnitude: 4.0, duration: 0.15, startAt: 10).events
        // Jump > maxSampleGap while still in burst; process should flush first.
        let events = c.process(magnitude: 0.05, at: 20)
        XCTAssertEqual(events.first?.severity, .impact)
        XCTAssertEqual(events.first?.at ?? -1, 10.0, accuracy: 0.05)
    }
}
