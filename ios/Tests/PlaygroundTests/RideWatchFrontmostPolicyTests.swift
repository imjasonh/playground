import XCTest
@testable import Playground

final class RideWatchFrontmostPolicyTests: XCTestCase {
    func testLaunchesImmediatelyOnFirstRideSnapshot() {
        XCTAssertTrue(
            RideWatchFrontmostPolicy.shouldLaunchWatch(
                didLaunchThisRide: false,
                lastLaunchAt: nil,
                now: Date()
            )
        )
    }

    func testDoesNotRelaunchBeforeInterval() {
        let last = Date(timeIntervalSince1970: 1_000)
        let now = last.addingTimeInterval(RideWatchFrontmostPolicy.relaunchInterval - 1)
        XCTAssertFalse(
            RideWatchFrontmostPolicy.shouldLaunchWatch(
                didLaunchThisRide: true,
                lastLaunchAt: last,
                now: now
            )
        )
    }

    func testRelaunchesAfterInterval() {
        let last = Date(timeIntervalSince1970: 1_000)
        let now = last.addingTimeInterval(RideWatchFrontmostPolicy.relaunchInterval)
        XCTAssertTrue(
            RideWatchFrontmostPolicy.shouldLaunchWatch(
                didLaunchThisRide: true,
                lastLaunchAt: last,
                now: now
            )
        )
    }

    func testRelaunchesWhenLastLaunchUnknown() {
        XCTAssertTrue(
            RideWatchFrontmostPolicy.shouldLaunchWatch(
                didLaunchThisRide: true,
                lastLaunchAt: nil,
                now: Date()
            )
        )
    }

    func testUnexpectedRestartRequiresWantedSessionAndUnderCap() {
        XCTAssertTrue(
            RideWatchFrontmostPolicy.shouldRestartAfterUnexpectedEnd(
                wantsSession: true,
                failureCount: 0
            )
        )
        XCTAssertFalse(
            RideWatchFrontmostPolicy.shouldRestartAfterUnexpectedEnd(
                wantsSession: false,
                failureCount: 0
            )
        )
        XCTAssertFalse(
            RideWatchFrontmostPolicy.shouldRestartAfterUnexpectedEnd(
                wantsSession: true,
                failureCount: RideWatchFrontmostPolicy.maxUnexpectedRestarts
            )
        )
    }

    func testRestartDelayBacksOff() {
        XCTAssertEqual(RideWatchFrontmostPolicy.restartDelay(afterFailureCount: 0), 1, accuracy: 0.001)
        XCTAssertEqual(RideWatchFrontmostPolicy.restartDelay(afterFailureCount: 1), 2, accuracy: 0.001)
        XCTAssertEqual(RideWatchFrontmostPolicy.restartDelay(afterFailureCount: 3), 8, accuracy: 0.001)
        XCTAssertEqual(RideWatchFrontmostPolicy.restartDelay(afterFailureCount: 99), 32, accuracy: 0.001)
    }
}
