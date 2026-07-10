import XCTest
@testable import Playground

final class HumHeadingFusionTests: XCTestCase {
    func testWorldOffsetAlignsYawToPhoneHeading() {
        let offset = HumHeadingFusion.worldOffsetDegrees(phoneHeading: 90, headYaw: 10)
        XCTAssertEqual(offset, 80, accuracy: 1e-9)
        let head = HumHeadingFusion.headHeadingDegrees(yaw: 10, worldOffset: offset)
        XCTAssertEqual(head, 90, accuracy: 1e-9)
    }

    func testHeadTurnUpdatesFacingWithoutNewPhoneReading() {
        var fusion = HumHeadingFusion()
        fusion.ingestPhoneHeading(0) // facing north
        fusion.ingestHeadYaw(0)
        XCTAssertTrue(fusion.isHeadLocked)
        XCTAssertEqual(fusion.facingDegrees()!, 0, accuracy: 1e-9)

        // Turn head 90° to the left in CM yaw space (yaw increases).
        fusion.ingestHeadYaw(90)
        // Facing should rotate with the head using the locked offset.
        XCTAssertEqual(fusion.facingDegrees()!, 90, accuracy: 1e-9)
        XCTAssertEqual(fusion.activeSource(), .airPodsHead)
    }

    func testIgnoresNeedForPhoneAfterLock() {
        var fusion = HumHeadingFusion()
        fusion.ingestPhoneHeading(45)
        fusion.ingestHeadYaw(0)
        XCTAssertEqual(fusion.facingDegrees()!, 45, accuracy: 1e-9)

        // Pocketed phone reports nonsense; we do not re-lock, but ingestPhoneHeading
        // still updates lastPhone — facing must keep using head+offset.
        fusion.ingestHeadYaw(20)
        let facingBeforeNoise = fusion.facingDegrees()!
        // Simulate session behavior: after lock, session won't call ingestPhoneHeading.
        // If it did call before lock-only guard, offset stays the first lock:
        XCTAssertEqual(fusion.worldOffsetDegrees!, 45, accuracy: 1e-9)
        XCTAssertEqual(facingBeforeNoise, HumHeadingFusion.headHeadingDegrees(yaw: 20, worldOffset: 45), accuracy: 1e-9)
    }

    func testPhoneOnlyFallbackBeforeHeadData() {
        var fusion = HumHeadingFusion()
        fusion.ingestPhoneHeading(120)
        XCTAssertFalse(fusion.isHeadLocked)
        XCTAssertEqual(fusion.facingDegrees()!, 120, accuracy: 1e-9)
        XCTAssertEqual(fusion.activeSource(), .phoneCompass)
    }

    func testResetClearsLock() {
        var fusion = HumHeadingFusion()
        fusion.ingestPhoneHeading(10)
        fusion.ingestHeadYaw(5)
        XCTAssertTrue(fusion.isHeadLocked)
        fusion.reset()
        XCTAssertFalse(fusion.isHeadLocked)
        XCTAssertNil(fusion.facingDegrees())
    }

    func testOffsetWrapsAcrossNorth() {
        let offset = HumHeadingFusion.worldOffsetDegrees(phoneHeading: 10, headYaw: 350)
        // 10 - 350 = -340 → normalize to 20
        XCTAssertEqual(offset, 20, accuracy: 1e-9)
        XCTAssertEqual(
            HumHeadingFusion.headHeadingDegrees(yaw: 350, worldOffset: offset),
            10,
            accuracy: 1e-9
        )
    }
}
