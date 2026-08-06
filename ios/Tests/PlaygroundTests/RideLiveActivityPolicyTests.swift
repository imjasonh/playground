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
}
