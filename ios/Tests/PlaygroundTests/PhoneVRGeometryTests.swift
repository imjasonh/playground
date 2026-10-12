import XCTest
import simd
@testable import Playground

final class PhoneVRGeometryTests: XCTestCase {
    private func assertEqual(_ a: SIMD3<Float>, _ b: SIMD3<Float>, accuracy: Float = 1e-4, file: StaticString = #filePath, line: UInt = #line) {
        XCTAssertLessThan(simd_length(a - b), accuracy, "\(a) != \(b)", file: file, line: line)
    }

    private func assertSameRotation(_ a: simd_quatf, _ b: simd_quatf, accuracy: Float = 1e-3, file: StaticString = #filePath, line: UInt = #line) {
        XCTAssertLessThan(VRMath.angleBetween(a, b), accuracy, file: file, line: line)
    }

    // MARK: - Math

    func testPoseCompositionAndInverse() {
        let a = VRPose(rotation: VRMath.rotationY(0.4), position: SIMD3(1, 2, 3))
        let b = VRPose(rotation: VRMath.rotationX(-0.3), position: SIMD3(-0.5, 0.25, 2))
        let p = SIMD3<Float>(0.3, -0.7, 1.1)
        assertEqual((a * b).transformPoint(p), a.transformPoint(b.transformPoint(p)))
        assertEqual((a * a.inverse).transformPoint(p), p)
        let fromMatrix = VRPose(a.matrix)
        assertEqual(fromMatrix.transformPoint(p), a.transformPoint(p))
    }

    func testRotationVectorRoundTrip() {
        let v = SIMD3<Float>(0.2, -0.5, 0.9)
        assertEqual(VRMath.rotationVector(of: VRMath.rotation(fromVector: v)), v)
        assertEqual(VRMath.rotationVector(of: VRMath.rotation(fromVector: .zero)), .zero)
    }

    func testIntegrateConstantBodyRate() {
        let start = VRMath.rotationX(0.5)
        let rate = SIMD3<Float>(0, 0, 2)
        let after = VRMath.integrate(start, bodyRate: rate, dt: 0.1)
        assertSameRotation(after, start * VRMath.rotationZ(0.2))
    }

    func testYawAboutUpIgnoresPitch() {
        let q = VRMath.rotationY(0.7) * VRMath.rotationX(0.3)
        XCTAssertEqual(VRMath.yawAboutUp(of: q), 0.7, accuracy: 1e-4)
        XCTAssertEqual(VRMath.yawAboutUp(of: VRMath.rotationY(-2.5)), -2.5, accuracy: 1e-4)
    }

    func testHeadingStaysDefinedLookingDown() {
        XCTAssertEqual(VRMath.heading(of: VRMath.rotationY(0.5)), 0.5, accuracy: 1e-4)
        let lookingDown = VRMath.rotationY(0.5) * VRMath.rotationX(VRMath.radians(-85))
        XCTAssertEqual(VRMath.heading(of: lookingDown), 0.5, accuracy: 1e-3)
        let straightDown = VRMath.rotationY(0.5) * VRMath.rotationX(-.pi / 2)
        XCTAssertEqual(VRMath.heading(of: straightDown), 0.5, accuracy: 1e-3)
        let straightUp = VRMath.rotationY(-1.2) * VRMath.rotationX(.pi / 2)
        XCTAssertEqual(VRMath.heading(of: straightUp), -1.2, accuracy: 1e-3)
    }

    func testPerspectiveMapsTangentCornersToNDC() {
        let tangents = VRTangents(left: -0.6, right: 0.4, bottom: -0.5, top: 0.55)
        let projection = VRMath.perspective(tangents, near: 0.05)
        let z: Float = -2
        let corner = projection * SIMD4(tangents.right * -z, tangents.top * -z, z, 1)
        XCTAssertEqual(corner.x / corner.w, 1, accuracy: 1e-5)
        XCTAssertEqual(corner.y / corner.w, 1, accuracy: 1e-5)
        let other = projection * SIMD4(tangents.left * -z, tangents.bottom * -z, z, 1)
        XCTAssertEqual(other.x / other.w, -1, accuracy: 1e-5)
        XCTAssertEqual(other.y / other.w, -1, accuracy: 1e-5)
        let near = projection * SIMD4(0, 0, -0.05, 1)
        XCTAssertEqual(near.z / near.w, 1, accuracy: 1e-5)
        let far = projection * SIMD4(0, 0, -1000, 1)
        XCTAssertLessThan(far.z / far.w, 1e-3)
        XCTAssertGreaterThan(far.z / far.w, 0)
    }

    func testTangentUVConventions() {
        let t = VRTangents(left: -1, right: 1, bottom: -0.5, top: 0.5)
        XCTAssertEqual(t.uv(fromTangent: SIMD2(-1, 0.5)), SIMD2(0, 0))
        XCTAssertEqual(t.uv(fromTangent: SIMD2(1, -0.5)), SIMD2(1, 1))
        XCTAssertEqual(t.tangent(fromUV: SIMD2(0.5, 0.5)), SIMD2(0, 0))
        let wider = VRTangents(left: -1, right: 1, bottom: -1, top: 1).expanded(byDegrees: 5)
        XCTAssertEqual(wider.right, tan(VRMath.radians(50)), accuracy: 1e-5)
        XCTAssertEqual(wider.left, -tan(VRMath.radians(50)), accuracy: 1e-5)
    }

    func testRingBufferKeepsNewestInOrder() {
        var ring = VRRingBuffer<Int>(capacity: 3)
        for i in 1...5 { ring.append(i) }
        XCTAssertEqual(ring.elements, [3, 4, 5])
        XCTAssertEqual(ring.first, 3)
        XCTAssertEqual(ring.last, 5)
        ring.removeAll()
        XCTAssertTrue(ring.isEmpty)
    }

    // MARK: - Panel and frames

    func testIPhone15ProPanelMatchesSketch() {
        let screen = VRPhoneScreen.iPhone15Pro
        XCTAssertEqual(screen.widthPixels, 2556)
        XCTAssertEqual(screen.heightPixels, 1179)
        XCTAssertEqual(screen.widthMeters * 1000, 141.1, accuracy: 0.1)
        XCTAssertEqual(screen.heightMeters * 1000, 65.1, accuracy: 0.1)
    }

    func testPhoneModelPixelDensities() {
        XCTAssertEqual(VRPhoneModel.lookup(identifier: "iPhone16,1", isPad: false).pixelsPerInch, 460)
        XCTAssertEqual(VRPhoneModel.lookup(identifier: "iPhone13,1", isPad: false).pixelsPerInch, 476)
        XCTAssertEqual(VRPhoneModel.lookup(identifier: "iPad14,1", isPad: true).pixelsPerInch, 264)
        XCTAssertEqual(VRPhoneModel.lookup(identifier: "iPhone99,9", isPad: false).pixelsPerInch, 460)
    }

    func testDeviceFromCameraMatchesARKitAxes() {
        let q = VRDeviceFrames.deviceFromCamera
        // ARKit: camera x runs from the front camera toward the bottom edge, z out of the screen.
        assertEqual(q.act(SIMD3(1, 0, 0)), SIMD3(0, -1, 0))
        assertEqual(q.act(SIMD3(0, 1, 0)), SIMD3(1, 0, 0))
        assertEqual(q.act(SIMD3(0, 0, 1)), SIMD3(0, 0, 1))
    }

    func testCoreMotionReferenceMapsToGravityWorld() {
        let q = VRDeviceFrames.worldFromReferenceBase
        assertEqual(q.act(SIMD3(0, 0, 1)), SIMD3(0, 1, 0))
        assertEqual(q.act(SIMD3(1, 0, 0)), SIMD3(1, 0, 0))
        assertEqual(q.act(SIMD3(0, 1, 0)), SIMD3(0, 0, -1))
    }

    func testCameraLeftMountingAlignsScreenWithCamera() {
        let frames = VRDeviceFrames(mounting: .cameraLeft)
        assertSameRotation(frames.screenFromCamera.rotation, VRMath.identityRotation)
        // Device top on the wearer's left puts the camera left of and above the panel centre.
        assertEqual(frames.screenFromCamera.position, SIMD3(-0.0513, 0.0133, -0.006))
        let roundTrip = frames.cameraFromScreen * frames.screenFromCamera
        assertEqual(roundTrip.position, .zero)
    }

    func testCameraRightMountingIsAHalfTurn() {
        let frames = VRDeviceFrames(mounting: .cameraRight)
        assertSameRotation(frames.screenFromCamera.rotation, VRMath.rotationZ(.pi))
        assertEqual(frames.screenFromCamera.position, SIMD3(0.0513, -0.0133, -0.006))
    }

    // MARK: - Viewer profile

    func testStandardProfileMatchesSketch() {
        let p = VRViewerProfile.standard
        XCTAssertEqual(p.screenToLensDistance, 0.042)
        XCTAssertEqual(p.interLensDistance, 0.0639)
        XCTAssertEqual(p.eyeToScreenDistance, 0.066, accuracy: 1e-6)
        XCTAssertEqual(p.fieldOfView, .symmetric(27))
        XCTAssertEqual(p.distortionK1, 0.441)
        XCTAssertEqual(p.distortionK2, 0.156)
        XCTAssertEqual(p.verticalAlignment, .center)
        XCTAssertEqual(p.virtualImageDistance ?? 0, 0.654, accuracy: 1e-3)
    }

    func testChromaticEstimateMatchesStandardScales() {
        let p = VRViewerProfile.standard
        let scales = VRViewerProfile.estimatedChromaticScales(
            screenToLens: p.screenToLensDistance,
            eyeRelief: p.eyeRelief,
            focalLength: p.lensFocalLength
        )
        XCTAssertEqual(scales.red, p.redScale, accuracy: 1e-4)
        XCTAssertEqual(scales.blue, p.blueScale, accuracy: 1e-4)
        let atLens = VRViewerProfile.estimatedChromaticScales(screenToLens: 0.042, eyeRelief: 0, focalLength: 0.045)
        XCTAssertEqual(atLens.red, 1, accuracy: 1e-6)
        XCTAssertEqual(atLens.blue, 1, accuracy: 1e-6)
    }

    func testProfileCodableRoundTripAndDefaults() throws {
        var p = VRViewerProfile.standard
        p.distortionK1 = 0.3
        p.verticalAlignment = .bottom
        let data = try JSONEncoder().encode(p)
        XCTAssertEqual(try JSONDecoder().decode(VRViewerProfile.self, from: data), p)
        let partial = Data(#"{"distortionK1": 0.25}"#.utf8)
        let decoded = try JSONDecoder().decode(VRViewerProfile.self, from: partial)
        XCTAssertEqual(decoded.distortionK1, 0.25)
        XCTAssertEqual(decoded.interLensDistance, VRViewerProfile.standard.interLensDistance)
    }

    func testProfileClampsOutOfRangeValues() {
        var p = VRViewerProfile.standard
        p.interLensDistance = 0.2
        p.redScale = 2
        p.fieldOfView.top = 120
        let c = p.clamped()
        XCTAssertEqual(c.interLensDistance, 0.080)
        XCTAssertEqual(c.redScale, 1.03)
        XCTAssertEqual(c.fieldOfView.top, 60)
    }

    // MARK: - Lens model

    func testDistortionInverseRoundTrips() {
        let d = VRRadialDistortion(k1: 0.441, k2: 0.156)
        for i in 0...40 {
            let r = Float(i) / 40
            XCTAssertEqual(d.undistort(d.distort(r)), r, accuracy: 1e-4)
        }
        let barrel = VRRadialDistortion(k1: -0.2, k2: 0.02)
        for i in 0...20 {
            let r = Float(i) / 40
            XCTAssertEqual(barrel.undistort(barrel.distort(r)), r, accuracy: 1e-4)
        }
        XCTAssertEqual(d.undistort(0), 0)
    }

    func testStandardLayoutMatchesSketch() {
        let layout = VRStereoLayout(screen: .iPhone15Pro, profile: .standard)
        // Lens axes sit 3.3 mm (about 61 px) inboard of each half's centre.
        XCTAssertEqual(layout.lensInboardOffsetPixels, 60.3, accuracy: 0.5)
        XCTAssertEqual(layout.displayPixelsPerDegree, 13.27, accuracy: 0.05)
        let left = layout[.left]
        let right = layout[.right]
        XCTAssertEqual(left.lensCenterPixels.x, 1278 - 578.6, accuracy: 0.5)
        XCTAssertEqual(right.lensCenterPixels.x, 1278 + 578.6, accuracy: 0.5)
        XCTAssertEqual(left.lensCenterPixels.y, 589.5, accuracy: 0.01)
        // ±27° field plus the 2° timewarp margin.
        XCTAssertEqual(left.fieldTangents.right, tan(VRMath.radians(27)), accuracy: 1e-5)
        XCTAssertEqual(left.bufferTangents.right, tan(VRMath.radians(29)), accuracy: 1e-5)
        XCTAssertEqual(left.bufferTangents.left, -tan(VRMath.radians(29)), accuracy: 1e-5)
        // Pincushion distortion shrinks the round field below the 775 px paraxial estimate.
        XCTAssertEqual(left.visibleRadiusPixels * 2, 703, accuracy: 3)
        XCTAssertEqual(layout.eyeBufferSize(resolution: 1024).width, 1024)
        XCTAssertEqual(layout.eyeBufferSize(resolution: 1024).height, 1024)
        XCTAssertEqual(layout.eyeBufferPixelsPerDegree(resolution: 1024), 16.1, accuracy: 0.1)
        let hidden = layout.hiddenAreaFraction(for: .left)
        XCTAssertGreaterThan(hidden, 0.12)
        XCTAssertLessThan(hidden, 0.22)
        XCTAssertEqual(left.eyeInScreen, SIMD3(-0.03195, 0, 0.066))
    }

    func testViewingTangentAndPixelAreInverse() {
        let layout = VRStereoLayout(screen: .iPhone15Pro, profile: .standard)
        for eye in VREye.allCases {
            let center = layout[eye].lensCenterPixels
            XCTAssertEqual(layout.viewingTangent(forPixel: center, eye: eye), SIMD2(0, 0))
            let t = SIMD2<Float>(0.3, -0.2)
            let pixel = layout.pixel(forViewingTangent: t, eye: eye)
            guard let back = layout.viewingTangent(forPixel: pixel, eye: eye) else {
                return XCTFail("pixel for an in-field tangent should map back")
            }
            XCTAssertLessThan(simd_length(back - t), 1e-4)
            // Up in view space is up on the panel: smaller y in drawable pixels.
            XCTAssertGreaterThan(pixel.y, center.y)
        }
        XCTAssertNil(layout.viewingTangent(forPixel: VRPhoneScreen.iPhone15Pro.centerPixels, eye: .left))
        XCTAssertNil(layout.viewingTangent(forPixel: SIMD2(5, 5), eye: .left))
    }

    func testBottomAlignmentMovesLensesDown() {
        var profile = VRViewerProfile.standard
        profile.verticalAlignment = .bottom
        profile.trayToLensDistance = 0.030
        let layout = VRStereoLayout(screen: .iPhone15Pro, profile: profile)
        let ppm = VRPhoneScreen.iPhone15Pro.pixelsPerMeter
        let expectedFromBottom = (0.030 - VRStereoLayout.trayBorder) * ppm
        XCTAssertEqual(Float(1179) - layout[.left].lensCenterPixels.y, expectedFromBottom, accuracy: 0.5)
        XCTAssertLessThan(layout[.left].eyeInScreen.y, 0)
    }

    func testViewerReportMatchesSketch() {
        let report = VRViewerReport(layout: VRStereoLayout(screen: .iPhone15Pro, profile: .standard))
        XCTAssertEqual(report.panelWidthMillimeters, 141.1, accuracy: 0.1)
        XCTAssertEqual(report.halfWidthPixels, 1278)
        XCTAssertEqual(report.lensInboardMillimeters, 3.33, accuracy: 0.03)
        XCTAssertEqual(report.eyeToScreenMillimeters, 66, accuracy: 0.01)
        XCTAssertEqual(report.displayPixelsPerDegree, 13.3, accuracy: 0.05)
    }
}
