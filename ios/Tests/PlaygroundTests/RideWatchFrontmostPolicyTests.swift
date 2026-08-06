import XCTest
@testable import Playground

final class RideWatchFrontmostPolicyTests: XCTestCase {
    func testRelaunchesImmediatelyWhenNeverLaunched() {
        XCTAssertTrue(
            RideWatchFrontmostPolicy.shouldRelaunchWatch(
                lastLaunchAt: nil,
                now: Date()
            )
        )
    }

    func testDoesNotRelaunchBeforeInterval() {
        let last = Date(timeIntervalSince1970: 1_000)
        let now = last.addingTimeInterval(RideWatchFrontmostPolicy.relaunchInterval - 1)
        XCTAssertFalse(
            RideWatchFrontmostPolicy.shouldRelaunchWatch(
                lastLaunchAt: last,
                now: now
            )
        )
    }

    func testRelaunchesAfterInterval() {
        let last = Date(timeIntervalSince1970: 1_000)
        let now = last.addingTimeInterval(RideWatchFrontmostPolicy.relaunchInterval)
        XCTAssertTrue(
            RideWatchFrontmostPolicy.shouldRelaunchWatch(
                lastLaunchAt: last,
                now: now
            )
        )
    }

    func testAttemptStartRequiresWantedSessionUnderCapAndCooldown() {
        let now = Date(timeIntervalSince1970: 1_000)

        XCTAssertTrue(
            RideWatchFrontmostPolicy.shouldAttemptStart(
                wantsSession: true,
                attemptCount: 0,
                lastAttemptAt: nil,
                now: now
            )
        )
        XCTAssertFalse(
            RideWatchFrontmostPolicy.shouldAttemptStart(
                wantsSession: false,
                attemptCount: 0,
                lastAttemptAt: nil,
                now: now
            )
        )
        XCTAssertFalse(
            RideWatchFrontmostPolicy.shouldAttemptStart(
                wantsSession: true,
                attemptCount: RideWatchFrontmostPolicy.maxStartAttemptsPerRide,
                lastAttemptAt: nil,
                now: now
            )
        )

        let recent = now.addingTimeInterval(-(RideWatchFrontmostPolicy.startAttemptCooldown - 1))
        XCTAssertFalse(
            RideWatchFrontmostPolicy.shouldAttemptStart(
                wantsSession: true,
                attemptCount: 1,
                lastAttemptAt: recent,
                now: now
            )
        )

        let cooled = now.addingTimeInterval(-RideWatchFrontmostPolicy.startAttemptCooldown)
        XCTAssertTrue(
            RideWatchFrontmostPolicy.shouldAttemptStart(
                wantsSession: true,
                attemptCount: 1,
                lastAttemptAt: cooled,
                now: now
            )
        )
    }
}
