import XCTest
import simd
@testable import Playground

final class PhoneVRHeadTrackerTests: XCTestCase {
    private let frames = VRDeviceFrames(mounting: .cameraLeft)
    private let bodyRate = SIMD3<Float>(0.4, -0.3, 0.8)
    private let startAttitude = VRMath.rotationX(1.3) * VRMath.rotationZ(0.2)

    private func makeTracker(prediction: Bool = true) -> VRHeadTracker {
        var configuration = VRHeadTracker.Configuration(frames: frames)
        configuration.predictionEnabled = prediction
        return VRHeadTracker(configuration: configuration)
    }

    private func attitude(at t: Double) -> simd_quatf {
        VRMath.integrate(startAttitude, bodyRate: bodyRate, dt: Float(t))
    }

    private func motion(at t: Double) -> VRMotionSample {
        VRMotionSample(timestamp: t, attitude: attitude(at: t), rotationRate: bodyRate)
    }

    /// What ARKit would report for the same device motion with Core Motion's
    /// reference frame yawed by `yaw` in the ARKit world.
    private func tracking(at t: Double, yaw: Float, position: SIMD3<Float>, quality: VRTrackingSample.Quality = .normal) -> VRTrackingSample {
        let worldFromCamera = VRDeviceFrames.worldFromReference(yaw: yaw) * attitude(at: t) * VRDeviceFrames.deviceFromCamera
        return VRTrackingSample(
            timestamp: t,
            worldFromCamera: VRPose(rotation: worldFromCamera, position: position).matrix,
            quality: quality
        )
    }

    private func expectedScreenRotation(at t: Double, yaw: Float) -> simd_quatf {
        VRDeviceFrames.worldFromReference(yaw: yaw) * attitude(at: t) * VRDeviceFrames.deviceFromCamera
            * frames.cameraFromScreen.rotation
    }

    private func feedMotion(_ tracker: inout VRHeadTracker, from start: Double, to end: Double) {
        var t = start
        while t <= end + 1e-9 {
            tracker.ingest(motion(at: t))
            t += 0.01
        }
    }

    func testAlignsCoreMotionYawToARKit() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 1)
        var t = 0.0
        while t < 0.98 {
            tracker.ingest(tracking(at: t, yaw: 0.8, position: SIMD3(0.1, 1.5, -0.2)))
            t += 1.0 / 60
        }
        XCTAssertTrue(tracker.hasYawOffset)
        XCTAssertEqual(tracker.yawOffset, 0.8, accuracy: 1e-3)
        XCTAssertEqual(tracker.mode, .sixDoF)
        let predicted = tracker.predictRotation(at: 1.0)
        XCTAssertLessThan(VRMath.angleBetween(predicted, expectedScreenRotation(at: 1.0, yaw: 0.8)), 1e-3)
    }

    func testPredictsAheadWithGyroRate() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 0.5)
        let predicted = tracker.predictHead(at: 0.52)
        XCTAssertEqual(predicted.rotationHorizon, 0.02, accuracy: 1e-6)
        XCTAssertLessThan(VRMath.angleBetween(predicted.worldFromScreen.rotation, expectedScreenRotation(at: 0.52, yaw: 0)), 1e-3)
    }

    func testPredictionOffHoldsNewestSample() {
        var tracker = makeTracker(prediction: false)
        feedMotion(&tracker, from: 0, to: 0.5)
        let held = tracker.predictHead(at: 0.52)
        XCTAssertEqual(held.rotationHorizon, 0)
        XCTAssertLessThan(VRMath.angleBetween(held.worldFromScreen.rotation, expectedScreenRotation(at: 0.5, yaw: 0)), 1e-3)
    }

    func testRotationHorizonIsClamped() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 0.5)
        let far = tracker.predictHead(at: 3)
        XCTAssertEqual(far.rotationHorizon, tracker.configuration.maxRotationHorizon, accuracy: 1e-9)
    }

    func testExtrapolatesARKitVelocity() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 1)
        var t = 0.0
        while t < 0.5 {
            tracker.ingest(tracking(at: t, yaw: 0, position: SIMD3(Float(t), 1.5, 0)))
            t += 1.0 / 60
        }
        let lastT = t - 1.0 / 60
        let lastScreen = (VRPose(tracking(at: lastT, yaw: 0, position: SIMD3(Float(lastT), 1.5, 0)).worldFromCamera)
            * frames.cameraFromScreen).position
        let predicted = tracker.predictHead(at: lastT + 0.03)
        XCTAssertEqual(predicted.translationHorizon, 0.03, accuracy: 1e-6)
        // The screen-centre velocity includes a little rotation of the camera offset, so allow a few mm.
        XCTAssertEqual(predicted.worldFromScreen.position.x, lastScreen.x + 0.03, accuracy: 0.004)
        XCTAssertEqual(predicted.worldFromScreen.position.y, lastScreen.y, accuracy: 0.004)
    }

    func testLimitedTrackingPivotsOnNeckWithoutAJump() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 0.3)
        tracker.ingest(tracking(at: 0.2, yaw: 0, position: SIMD3(0.5, 1.6, -1)))
        tracker.ingest(tracking(at: 0.25, yaw: 0, position: SIMD3(0.5, 1.6, -1)))
        let before = tracker.predictHead(at: 0.3).worldFromScreen
        tracker.ingest(tracking(at: 0.3, yaw: 0, position: SIMD3(9, 9, 9), quality: .limited))
        XCTAssertEqual(tracker.mode, .threeDoF)
        let after = tracker.predictHead(at: 0.3).worldFromScreen
        XCTAssertLessThan(simd_length(after.position - before.position), 1e-3)

        // Keep turning: the screen centre swings around the neck pivot.
        feedMotion(&tracker, from: 0.31, to: 0.8)
        let later = tracker.predictHead(at: 0.8).worldFromScreen
        let pivot = before.position - before.rotation.act(tracker.configuration.neckToScreen)
        let expected = pivot + later.rotation.act(tracker.configuration.neckToScreen)
        XCTAssertLessThan(simd_length(later.position - expected), 1e-3)
    }

    func testFirstARKitFixSnaps() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 1)
        tracker.ingest(tracking(at: 0.5, yaw: 0, position: SIMD3(2, 1.5, 0)))
        let arkit = (VRPose(tracking(at: 0.5, yaw: 0, position: SIMD3(2, 1.5, 0)).worldFromCamera) * frames.cameraFromScreen).position
        XCTAssertLessThan(simd_length(tracker.predictHead(at: 0.5).worldFromScreen.position - arkit), 1e-4)
    }

    func testReturningToSixDoFGlidesToTheARKitPosition() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 2)
        tracker.ingest(tracking(at: 0.1, yaw: 0, position: SIMD3(0, 1.5, 0)))
        tracker.ingest(tracking(at: 0.2, yaw: 0, position: SIMD3(0, 1.5, 0)))
        tracker.ingest(tracking(at: 0.3, yaw: 0, position: SIMD3(0, 1.5, 0), quality: .limited))
        XCTAssertEqual(tracker.mode, .threeDoF)
        let neckPosition = tracker.predictHead(at: 0.5).worldFromScreen.position
        tracker.ingest(tracking(at: 0.5, yaw: 0, position: SIMD3(2, 1.5, 0)))
        XCTAssertEqual(tracker.mode, .sixDoF)
        let immediately = tracker.predictHead(at: 0.5).worldFromScreen.position
        XCTAssertLessThan(simd_length(immediately - neckPosition), 1e-3)
        var t = 0.5
        while t < 1.9 {
            t += 1.0 / 60
            tracker.ingest(tracking(at: t, yaw: 0, position: SIMD3(2, 1.5, 0)))
        }
        let settled = tracker.predictHead(at: t).worldFromScreen.position
        let arkit = (VRPose(tracking(at: t, yaw: 0, position: SIMD3(2, 1.5, 0)).worldFromCamera) * frames.cameraFromScreen).position
        XCTAssertLessThan(simd_length(settled - arkit), 0.01)
    }

    func testRelocalizationJumpGlidesInsteadOfPopping() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 2)
        var t = 0.0
        while t < 0.5 {
            tracker.ingest(tracking(at: t, yaw: 0, position: SIMD3(0, 1.5, 0)))
            t += 1.0 / 60
        }
        let before = tracker.predictHead(at: t).worldFromScreen.position
        tracker.ingest(tracking(at: t, yaw: 0, position: SIMD3(1, 1.5, 0)))
        let atJump = tracker.predictHead(at: t).worldFromScreen.position
        XCTAssertLessThan(simd_length(atJump - before), 0.05)
        for _ in 0..<90 {
            t += 1.0 / 60
            tracker.ingest(tracking(at: t, yaw: 0, position: SIMD3(1, 1.5, 0)))
        }
        XCTAssertEqual(tracker.predictHead(at: t).worldFromScreen.position.x, 1, accuracy: 0.08)
    }

    func testYawCatchesUpAfterARKitWorldRotates() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 1.2)
        var t = 0.0
        while t < 0.2 {
            tracker.ingest(tracking(at: t, yaw: 0.2, position: .zero))
            t += 1.0 / 60
        }
        XCTAssertEqual(tracker.yawOffset, 0.2, accuracy: 1e-3)
        while t < 1.15 {
            tracker.ingest(tracking(at: t, yaw: 0.2 + VRMath.radians(20), position: .zero))
            t += 1.0 / 60
        }
        // Not snapped: rotating the world in one frame would be jarring.
        let error = abs(VRMath.wrapAngle(tracker.yawOffset - (0.2 + VRMath.radians(20))))
        XCTAssertLessThan(error, VRMath.radians(10))
        XCTAssertGreaterThan(tracker.yawOffset, 0.2 + VRMath.radians(5))
    }

    func testAttitudeInterpolatesBetweenSamples() {
        var tracker = makeTracker()
        feedMotion(&tracker, from: 0, to: 0.5)
        guard let mid = tracker.attitude(at: 0.255) else { return XCTFail("expected an interpolated attitude") }
        XCTAssertLessThan(VRMath.angleBetween(mid, attitude(at: 0.255)), 1e-3)
        XCTAssertNil(tracker.attitude(at: -1))
        XCTAssertNil(tracker.attitude(at: 0.6))
    }

    func testIgnoresDuplicateMotionSamples() {
        var tracker = makeTracker()
        tracker.ingest(motion(at: 0.1))
        tracker.ingest(motion(at: 0.1))
        tracker.ingest(motion(at: 0.05))
        XCTAssertEqual(tracker.latestMotion?.timestamp, 0.1)
    }
}
