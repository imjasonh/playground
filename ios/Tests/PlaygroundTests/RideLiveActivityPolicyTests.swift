import XCTest
@testable import Playground

final class RideLiveActivityPolicyTests: XCTestCase {
    func testEndsOrphansWhenIdle() {
        XCTAssertTrue(
            RideLiveActivityPolicy.shouldEndOrphans(
                hasTrackedActivity: false,
                hasPendingStart: false
            )
        )
    }

    func testKeepsActivityWhileTracking() {
        XCTAssertFalse(
            RideLiveActivityPolicy.shouldEndOrphans(
                hasTrackedActivity: true,
                hasPendingStart: false
            )
        )
    }

    func testKeepsActivityWhileStartPending() {
        XCTAssertFalse(
            RideLiveActivityPolicy.shouldEndOrphans(
                hasTrackedActivity: false,
                hasPendingStart: true
            )
        )
    }

    func testKeepsActivityWhileTrackingAndPending() {
        XCTAssertFalse(
            RideLiveActivityPolicy.shouldEndOrphans(
                hasTrackedActivity: true,
                hasPendingStart: true
            )
        )
    }

    func testSummaryRetentionIsThirtyMinutes() {
        XCTAssertEqual(RideLiveActivityPolicy.summaryRetention, 30 * 60)
    }

    func testSummaryDismissalDateAddsRetention() {
        let end = Date(timeIntervalSince1970: 1_700_000_000)
        let dismissal = RideLiveActivityPolicy.summaryDismissalDate(from: end)
        XCTAssertEqual(
            dismissal.timeIntervalSince(end),
            RideLiveActivityPolicy.summaryRetention,
            accuracy: 0.001
        )
    }

    func testEndedTimerIntervalIsClosedAtElapsedEnd() {
        let startedAt = Date(timeIntervalSince1970: 1_700_000_000)
        let interval = RideLiveActivityPolicy.endedTimerInterval(
            startedAt: startedAt,
            elapsedSeconds: 125
        )
        XCTAssertEqual(interval.lowerBound, startedAt)
        XCTAssertEqual(interval.upperBound.timeIntervalSince(startedAt), 125, accuracy: 0.001)
    }

    func testEndedTimerIntervalClampsNegativeElapsed() {
        let startedAt = Date(timeIntervalSince1970: 1_700_000_000)
        let interval = RideLiveActivityPolicy.endedTimerInterval(
            startedAt: startedAt,
            elapsedSeconds: -5
        )
        XCTAssertEqual(interval.lowerBound, startedAt)
        XCTAssertEqual(interval.upperBound, startedAt)
    }
}
