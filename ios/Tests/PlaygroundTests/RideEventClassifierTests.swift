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

    func testShakeIsClassifiedAsShake() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        all += feed(&c, magnitude: 0.8, duration: 0.1, startAt: 1).events   // above shake, below pothole
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 1.1).events
        XCTAssertEqual(all.count, 1)
        XCTAssertEqual(all.first?.severity, .shake)
    }

    func testPotholeIsClassifiedAsPothole() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        all += feed(&c, magnitude: 1.6, duration: 0.1, startAt: 1).events
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 1.1).events
        XCTAssertEqual(all.map(\.severity), [.pothole])
        XCTAssertGreaterThanOrEqual(all.first?.peakG ?? 0, 1.2)
    }

    func testHardImpactBelowCrashThresholdDoesNotBecomeCrash() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        all += feed(&c, magnitude: 3.2, duration: 0.1, startAt: 1).events   // impact but < crashImpact 3.5
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
        // Two spikes 0.1s apart — within the 0.4s debounce → one event.
        all += feed(&c, magnitude: 1.5, duration: 0.06, startAt: 1.0).events
        all += feed(&c, magnitude: 0.05, duration: 0.1, startAt: 1.06).events
        all += feed(&c, magnitude: 1.5, duration: 0.06, startAt: 1.16).events
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 1.22).events
        XCTAssertEqual(all.count, 1)
    }

    func testSeparateBumpsBeyondDebounceAreDistinctEvents() {
        var c = RideEventClassifier()
        var all: [RideEvent] = []
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 0).events
        all += feed(&c, magnitude: 1.5, duration: 0.06, startAt: 1.0).events
        all += feed(&c, magnitude: 0.05, duration: 1.0, startAt: 1.06).events   // well beyond debounce
        all += feed(&c, magnitude: 1.5, duration: 0.06, startAt: 2.1).events
        all += feed(&c, magnitude: 0.05, duration: 1, startAt: 2.16).events
        XCTAssertEqual(all.count, 2)
    }
}
