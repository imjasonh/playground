import XCTest
import simd
@testable import Playground

final class PhoneVRControlTests: XCTestCase {
    // MARK: - Play space

    func testRecenterFacesSceneForwardAndFindsFloor() {
        var space = VRPlaySpace()
        let head = VRPose(rotation: VRMath.rotationY(0.6) * VRMath.rotationX(-0.3), position: SIMD3(2, 1.7, -1))
        space.recenter(head: head)
        let sceneHead = space.sceneFromWorld * head
        XCTAssertEqual(sceneHead.position.x, 0, accuracy: 1e-5)
        XCTAssertEqual(sceneHead.position.z, 0, accuracy: 1e-5)
        XCTAssertEqual(sceneHead.position.y, 1.6, accuracy: 1e-5)
        XCTAssertEqual(VRMath.heading(of: sceneHead.rotation), 0, accuracy: 1e-4)
        space.setFloorHeight(0.05)
        XCTAssertEqual((space.sceneFromWorld * head).position.y, 1.65, accuracy: 1e-5)
    }

    func testSnapTurnRightBringsRightSideToTheFront() {
        var space = VRPlaySpace()
        let head = VRPose(rotation: VRMath.identityRotation, position: SIMD3(0.5, 1.6, 0.5))
        space.recenter(head: head)
        // A scene point to the wearer's right…
        let rightPoint = SIMD3<Float>(1, 1.6, 0)
        space.snapTurn(by: .pi / 2, head: head)
        // …ends up in front of the head after turning right.
        let world = space.worldFromScene.transformPoint(rightPoint)
        let inHead = head.inverse.transformPoint(world)
        XCTAssertEqual(inHead.x, 0, accuracy: 1e-4)
        XCTAssertEqual(inHead.z, -1, accuracy: 1e-4)
        // The head doesn't move in the scene.
        XCTAssertEqual(simd_length((space.sceneFromWorld * head).position - SIMD3(0, 1.6, 0)), 0, accuracy: 1e-4)
    }

    func testStickMovesWearerAlongHeading() {
        var space = VRPlaySpace()
        let head = VRPose(rotation: VRMath.rotationY(.pi / 2), position: SIMD3(0, 1.6, 0))
        space.recenter(head: head)
        let turnedHead = VRPose(rotation: VRMath.rotationY(.pi), position: SIMD3(0, 1.6, 0))
        space.move(stick: SIMD2(0, 1), speed: 2, dt: 0.5, head: turnedHead)
        // Scene heading is world heading minus the recenter yaw: the head now faces scene -X.
        let sceneHead = space.sceneFromWorld * turnedHead
        XCTAssertEqual(sceneHead.position.x, -1, accuracy: 1e-4)
        XCTAssertEqual(sceneHead.position.z, 0, accuracy: 1e-4)
    }

    func testBoundaryStaysFixedToTheRoom() {
        var space = VRPlaySpace()
        space.boundaryRadius = 1.5
        space.recenter(head: VRPose(rotation: VRMath.identityRotation, position: SIMD3(1, 1.6, 1)))
        XCTAssertEqual(space.boundaryDistance(head: SIMD3(1, 1.6, 1)), 1.5, accuracy: 1e-5)
        space.move(stick: SIMD2(0, 1), speed: 1, dt: 3, head: .identity)
        XCTAssertEqual(space.boundaryDistance(head: SIMD3(1, 1.6, 1)), 1.5, accuracy: 1e-5)
        XCTAssertEqual(space.boundaryDistance(head: SIMD3(3, 1.6, 1)), -0.5, accuracy: 1e-5)
    }

    // MARK: - Governor

    func testThermalTiersFollowTheSketch() {
        let governor = VRFrameGovernor(configuration: .init())
        XCTAssertEqual(governor.tier, VRRenderTier(refreshRate: 120, eyeResolution: 1024, reducedScene: false))
        XCTAssertEqual(governor.cap(for: .fair, lowPower: false).refreshRate, 120)
        XCTAssertEqual(VRFrameGovernor.resolutionLadder[governor.cap(for: .fair, lowPower: false).resolutionIndex], 896)
        XCTAssertEqual(governor.cap(for: .serious, lowPower: false).refreshRate, 60)
        XCTAssertEqual(VRFrameGovernor.resolutionLadder[governor.cap(for: .serious, lowPower: false).resolutionIndex], 768)
        XCTAssertEqual(governor.cap(for: .nominal, lowPower: true).refreshRate, 60)
    }

    func testHeatingAppliesAtOnceAndCoolingWaits() {
        var governor = VRFrameGovernor(configuration: .init())
        XCTAssertTrue(governor.update(now: 0, thermal: .serious, lowPower: false, gpuFrameTime: nil))
        XCTAssertEqual(governor.tier.refreshRate, 60)
        XCTAssertEqual(governor.tier.eyeResolution, 768)
        XCTAssertFalse(governor.update(now: 1, thermal: .nominal, lowPower: false, gpuFrameTime: nil))
        XCTAssertFalse(governor.update(now: 15, thermal: .nominal, lowPower: false, gpuFrameTime: nil))
        XCTAssertEqual(governor.tier.refreshRate, 60)
        XCTAssertTrue(governor.update(now: 21.5, thermal: .nominal, lowPower: false, gpuFrameTime: nil))
        XCTAssertEqual(governor.tier.refreshRate, 120)
        governor.update(now: 30, thermal: .critical, lowPower: false, gpuFrameTime: nil)
        XCTAssertTrue(governor.tier.reducedScene)
        XCTAssertEqual(governor.tier.eyeResolution, 640)
    }

    func testGPUTimeStepsResolutionWithinTheCap() {
        var governor = VRFrameGovernor(configuration: .init())
        let interval = 1.0 / 120
        governor.update(now: 0, thermal: .nominal, lowPower: false, gpuFrameTime: interval * 0.95)
        governor.update(now: 0.6, thermal: .nominal, lowPower: false, gpuFrameTime: interval * 0.95)
        XCTAssertEqual(governor.tier.eyeResolution, 896)
        for step in 0..<20 {
            governor.update(now: 1 + Double(step), thermal: .nominal, lowPower: false, gpuFrameTime: interval * 0.3)
        }
        // Steps back up but never past the wearer's 1024 cap.
        XCTAssertEqual(governor.tier.eyeResolution, 1024)
    }

    func testBudgetMatchesSketchTable() {
        let b = VRFrameBudget(refreshRate: 120, eyeResolution: 1024)
        XCTAssertEqual(b.frameIntervalMilliseconds, 8.333, accuracy: 0.001)
        XCTAssertEqual(b.gpuTotalMilliseconds, 6.667, accuracy: 0.001)
        XCTAssertEqual(b.eyePassMilliseconds, 5.667, accuracy: 0.001)
        XCTAssertEqual(b.cpuMilliseconds, 4.167, accuracy: 0.001)
        XCTAssertEqual(b.eyeMegapixelsPerFrame, 2.10, accuracy: 0.005)
        XCTAssertEqual(b.eyeMegapixelsPerSecond, 252, accuracy: 0.5)
        XCTAssertEqual(b.nativePanelMegapixelsPerSecond, 361.2, accuracy: 0.1)
        XCTAssertEqual(b.centerPixelsPerDegree, 16.1, accuracy: 0.05)
        XCTAssertEqual(VRFrameBudget(refreshRate: 60, eyeResolution: 768).frameIntervalMilliseconds, 16.667, accuracy: 0.001)
    }

    func testLateLatchWaitsForTheEyePassButNotPastTheDeadline() {
        let latch = VRLateLatch()
        let wait = latch.waitDuration(now: 0, deadline: 0.008, eyePassGPUTime: 0.004, finalPassGPUTime: 0.001)
        XCTAssertEqual(wait, 0.004 - latch.encodeTime, accuracy: 1e-9)
        let squeezed = latch.waitDuration(now: 0, deadline: 0.005, eyePassGPUTime: 0.006, finalPassGPUTime: 0.001)
        XCTAssertEqual(squeezed, 0.005 - 0.001 - latch.encodeTime - latch.safetyMargin, accuracy: 1e-9)
        XCTAssertEqual(latch.waitDuration(now: 0, deadline: 0.002, eyePassGPUTime: 0.004, finalPassGPUTime: 0.001), 0)
        var off = latch
        off.enabled = false
        XCTAssertEqual(off.waitDuration(now: 0, deadline: 0.008, eyePassGPUTime: 0.004, finalPassGPUTime: 0.001), 0)
    }

    // MARK: - Gaze

    func testGazeDwellFiresOnceThenRepeatsAfterRearm() {
        var dwell = VRGazeDwell<String>(dwellDuration: 1, rearmDelay: 0.5)
        var fired: [String] = []
        for _ in 0..<9 {
            if let hit = dwell.update(target: "recenter", dt: 0.1) { fired.append(hit) }
        }
        XCTAssertTrue(fired.isEmpty)
        XCTAssertEqual(dwell.progress, 0.9, accuracy: 1e-5)
        if let hit = dwell.update(target: "recenter", dt: 0.1) { fired.append(hit) }
        XCTAssertEqual(fired, ["recenter"])
        XCTAssertEqual(dwell.progress, 0)
        // Rearm (0.5 s) plus a second dwell (1 s) fits in 20 more frames; a third doesn't.
        for _ in 0..<20 {
            if let hit = dwell.update(target: "recenter", dt: 0.1) { fired.append(hit) }
        }
        XCTAssertEqual(fired, ["recenter", "recenter"])
    }

    func testGazeDwellResetsWhenTheGazeMoves() {
        var dwell = VRGazeDwell<String>(dwellDuration: 1)
        _ = dwell.update(target: "a", dt: 0.8)
        XCTAssertNil(dwell.update(target: "b", dt: 0.1))
        XCTAssertEqual(dwell.progress, 0.1, accuracy: 1e-5)
        XCTAssertNil(dwell.update(target: nil, dt: 0.1))
        XCTAssertEqual(dwell.progress, 0)
    }

    // MARK: - AirPods cross-check

    func testJacobiEigenReconstructsMatrix() {
        let m: [[Double]] = [[4, 1, 0.5, 0], [1, 3, 0, 0.2], [0.5, 0, 2, 0.1], [0, 0.2, 0.1, 1]]
        let (values, vectors) = VRSignalAlignment.symmetricEigen(m)
        for i in 0..<4 {
            for j in 0..<4 {
                var sum = 0.0
                for k in 0..<4 { sum += vectors[i][k] * values[k] * vectors[j][k] }
                XCTAssertEqual(sum, m[i][j], accuracy: 1e-9)
            }
        }
    }

    func testHornFitRecoversRotation() {
        let truth = (VRMath.rotationY(0.7) * VRMath.rotationX(-0.4) * VRMath.rotationZ(1.1)).normalized
        var source: [SIMD3<Float>] = []
        var target: [SIMD3<Float>] = []
        for i in 0..<60 {
            let f = Float(i)
            let v = SIMD3<Float>(sin(f * 0.37), cos(f * 0.23), sin(f * 0.11 + 1))
            source.append(v)
            target.append(truth.act(v))
        }
        guard let fit = VRSignalAlignment.fitRotation(from: source, to: target) else { return XCTFail("fit failed") }
        XCTAssertLessThan(VRMath.angleBetween(fit.rotation, truth), 1e-3)
        XCTAssertGreaterThan(fit.confidence, 0.3)
    }

    /// Synthetic rigid head: phone at 100 Hz, AirPods at 25 Hz whose
    /// timestamps run `podsDelay` late, turned by `mount` relative to the phone.
    private struct SyntheticHead {
        let mount = (VRMath.rotationZ(0.5) * VRMath.rotationX(1.2)).normalized
        let podsDelay = 0.08
        var phoneAttitude = VRMath.rotationX(1.3)
        let podsStart = VRMath.rotationY(0.4)
        var phoneStart = VRMath.rotationX(1.3)
        var phone: [VRRotationSample] = []
        var pods: [VRRotationSample] = []
        var time = 0.0
        var slip = VRMath.identityRotation

        func headRate(_ t: Double, moving: Bool) -> SIMD3<Float> {
            guard moving else { return .zero }
            let t = Float(t)
            return SIMD3(1.2 * sin(2.1 * t), 0.9 * sin(1.3 * t + 0.5), 1.5 * sin(0.7 * t + 1.1) + 0.4 * sin(3.3 * t))
        }

        mutating func run(seconds: Double, moving: Bool) {
            let dt = 0.001
            let end = time + seconds
            while time < end - 1e-9 {
                let rate = headRate(time, moving: moving)
                phoneAttitude = VRMath.integrate(phoneAttitude, bodyRate: rate, dt: Float(dt))
                time += dt
                let step = Int((time * 1000).rounded())
                if step % 10 == 0 {
                    phone.append(VRRotationSample(timestamp: time, rate: rate, attitude: (phoneAttitude * slip).normalized))
                }
                if step % 40 == 0 {
                    let phoneDelta = phoneStart.inverse * phoneAttitude
                    let podsAttitude = podsStart * (mount.inverse * phoneDelta * mount)
                    pods.append(VRRotationSample(timestamp: time + podsDelay, rate: mount.inverse.act(rate), attitude: podsAttitude.normalized))
                }
            }
        }
    }

    func testCrossCheckEstimatesLatencyAndMount() {
        var head = SyntheticHead()
        var check = VRHeadphoneCrossCheck()
        var snapshot = check.update(phone: [], pods: [], podsLocation: 1, now: 0, currentYawBias: 0)
        XCTAssertEqual(snapshot.status, .waitingForAirPods)
        for second in 1...8 {
            head.run(seconds: 1, moving: true)
            snapshot = check.update(phone: head.phone, pods: head.pods, podsLocation: 1, now: head.time + head.podsDelay, currentYawBias: 0)
            if second == 1 { XCTAssertEqual(snapshot.status, .waitingForAirPods) }
        }
        XCTAssertEqual(snapshot.status, .aligned)
        XCTAssertEqual(snapshot.latency ?? 0, head.podsDelay, accuracy: 0.01)
        XCTAssertEqual(snapshot.updateRateHz ?? 0, 25, accuracy: 0.5)
        guard let mount = check.mountRotation else { return XCTFail("expected a mount estimate") }
        XCTAssertLessThan(VRMath.degrees(VRMath.angleBetween(mount, head.mount)), 2)
        XCTAssertLessThan(snapshot.residualDegrees ?? 99, 1.5)
        XCTAssertEqual(snapshot.slipCount, 0)
    }

    func testCrossCheckFlagsViewerSlip() {
        var head = SyntheticHead()
        var check = VRHeadphoneCrossCheck()
        for _ in 1...8 {
            head.run(seconds: 1, moving: true)
            _ = check.update(phone: head.phone, pods: head.pods, podsLocation: 1, now: head.time + head.podsDelay, currentYawBias: 0)
        }
        // Hold still, then the viewer slips 7° on the face.
        var snapshot = check.update(phone: head.phone, pods: head.pods, podsLocation: 1, now: head.time + head.podsDelay, currentYawBias: 0)
        for _ in 0..<3 {
            head.run(seconds: 1, moving: false)
            snapshot = check.update(phone: head.phone, pods: head.pods, podsLocation: 1, now: head.time + head.podsDelay, currentYawBias: 0)
        }
        XCTAssertEqual(snapshot.slipCount, 0)
        head.slip = VRMath.rotationX(VRMath.radians(7))
        for _ in 0..<3 {
            head.run(seconds: 1, moving: false)
            snapshot = check.update(phone: head.phone, pods: head.pods, podsLocation: 1, now: head.time + head.podsDelay, currentYawBias: 0)
        }
        XCTAssertEqual(snapshot.slipCount, 1)
        XCTAssertNotNil(snapshot.lastSlipTime)
    }

    func testCrossCheckRestartsWhenTheEarbudChanges() {
        var head = SyntheticHead()
        var check = VRHeadphoneCrossCheck()
        for _ in 1...6 {
            head.run(seconds: 1, moving: true)
            _ = check.update(phone: head.phone, pods: head.pods, podsLocation: 1, now: head.time + head.podsDelay, currentYawBias: 0)
        }
        XCTAssertNotNil(check.latency)
        head.run(seconds: 1, moving: true)
        let snapshot = check.update(phone: head.phone, pods: head.pods, podsLocation: 2, now: head.time + head.podsDelay, currentYawBias: 0)
        XCTAssertEqual(snapshot.status, .waitingForAirPods)
        XCTAssertNil(check.latency)
        XCTAssertNil(check.mountRotation)
    }
}
