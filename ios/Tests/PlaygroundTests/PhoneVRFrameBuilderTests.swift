import XCTest
import simd
@testable import Playground

final class PhoneVRFrameBuilderTests: XCTestCase {
    private let layout = VRStereoLayout(screen: .iPhone15Pro, profile: .standard)
    private let head = VRPose(rotation: VRMath.identityRotation, position: SIMD3(0, 1.6, 0))

    private func ndc(_ point: SIMD3<Float>, _ uniforms: VREyeUniforms) -> SIMD3<Float> {
        let clip = uniforms.viewProjection * SIMD4(point, 1)
        return SIMD3(clip.x, clip.y, clip.z) / clip.w
    }

    func testShaderStructSizesMatchMetal() {
        XCTAssertEqual(MemoryLayout<VREyeUniforms>.size, 160)
        XCTAssertEqual(MemoryLayout<VRFrameUniforms>.size, 128)
        XCTAssertEqual(MemoryLayout<VRInstanceUniforms>.size, 96)
        XCTAssertEqual(MemoryLayout<VRPanelUniforms>.size, 96)
        XCTAssertEqual(MemoryLayout<VRPassthroughUniforms>.size, 80)
        XCTAssertEqual(MemoryLayout<VRDistortionEyeUniforms>.size, 112)
        XCTAssertEqual(MemoryLayout<VRDistortionEyeUniforms>.offset(of: \VRDistortionEyeUniforms.lensCenter), 48)
        XCTAssertEqual(MemoryLayout<VRDistortionFrameUniforms>.size, 64)
    }

    func testNearObjectsAppearInboardInEachEye() {
        let eyes = VRFrameBuilder.eyeUniforms(layout: layout, sceneFromHead: head)
        let near = head.position + SIMD3(0, 0, -0.5)
        let far = head.position + SIMD3(0, 0, -1000)
        // Straight ahead at infinity sits on each lens axis.
        XCTAssertEqual(ndc(far, eyes[0]).x, 0, accuracy: 1e-3)
        XCTAssertEqual(ndc(far, eyes[1]).x, 0, accuracy: 1e-3)
        // Something close and centred is right of the left eye's axis and left of the right eye's.
        XCTAssertGreaterThan(ndc(near, eyes[0]).x, 0.05)
        XCTAssertLessThan(ndc(near, eyes[1]).x, -0.05)
        // Above is up, in front is inside the depth range.
        let above = ndc(head.position + SIMD3(0, 0.3, -2), eyes[0])
        XCTAssertGreaterThan(above.y, 0)
        XCTAssertGreaterThan(above.z, 0)
        XCTAssertLessThan(above.z, 1)
    }

    func testInverseViewProjectionUndoesTheProjection() {
        let turned = VRPose(rotation: VRMath.rotationY(0.7) * VRMath.rotationX(-0.2), position: SIMD3(1, 1.5, -2))
        for eye in VRFrameBuilder.eyeUniforms(layout: layout, sceneFromHead: turned) {
            let identity = eye.inverseViewProjection * eye.viewProjection
            for c in 0..<4 {
                for r in 0..<4 {
                    XCTAssertEqual(identity[c][r], c == r ? 1 : 0, accuracy: 1e-3)
                }
            }
        }
    }

    func testSkyDirectionPointsWhereTheEyeLooks() {
        let turned = VRPose(rotation: VRMath.rotationY(0.5), position: SIMD3(0, 1.6, 0))
        let eye = VRFrameBuilder.eyeUniforms(layout: layout, sceneFromHead: turned)[0]
        let d = eye.inverseViewProjection * SIMD4<Float>(0, 0, 0, 1)
        let direction = simd_normalize(SIMD3(d.x, d.y, d.z))
        let expected = turned.rotation.act(SIMD3(0, 0, -1))
        XCTAssertGreaterThan(simd_dot(direction, expected), 0.999)
    }

    func testTimewarpCompensatesALateHeadTurn() {
        let buffer = layout[.left].bufferTangents
        let identity = VRFrameBuilder.timewarpRotation(rendered: head.rotation, late: head.rotation)
        let t = SIMD2<Float>(0.2, -0.1)
        guard let same = VRFrameBuilder.timewarpedUV(tangent: t, rotation: identity, buffer: buffer) else { return XCTFail("expected a sample") }
        XCTAssertLessThan(simd_length(same - buffer.uv(fromTangent: t)), 1e-5)

        // The head turned 2° right after rendering: what was dead ahead now
        // shows 2° left of centre, and timewarp must sample the old centre there.
        let angle = VRMath.radians(2)
        let late = (head.rotation * VRMath.rotationY(-angle)).normalized
        let rotation = VRFrameBuilder.timewarpRotation(rendered: head.rotation, late: late)
        guard let uv = VRFrameBuilder.timewarpedUV(tangent: SIMD2(-tan(angle), 0), rotation: rotation, buffer: buffer) else {
            return XCTFail("expected a sample")
        }
        XCTAssertLessThan(simd_length(uv - buffer.uv(fromTangent: .zero)), 1e-4)
    }

    func testPassthroughQuadMatchesTheCameraFrustum() {
        var intrinsics = matrix_identity_float3x3
        intrinsics[0][0] = 1000
        intrinsics[1][1] = 1000
        intrinsics[2][0] = 960
        intrinsics[2][1] = 720
        let uniforms = VRFrameBuilder.passthroughUniforms(
            sceneFromCamera: .identity, intrinsics: intrinsics, imageWidth: 1920, imageHeight: 1440, distance: 2, opacity: 0.5
        )
        XCTAssertEqual(uniforms.corner0, SIMD4(-1.92, 1.44, -2, 1))
        XCTAssertEqual(uniforms.corner3, SIMD4(1.92, -1.44, -2, 1))
        XCTAssertEqual(uniforms.tint.w, 0.5)
    }

    func testDistortionUniformsMirrorTheLayout() {
        let eyes = VRFrameBuilder.distortionEyes(layout: layout, timewarp: VRMath.identityRotation, vignette: 0.8)
        XCTAssertEqual(eyes.count, 2)
        for eye in VREye.allCases {
            let u = eyes[eye.rawValue]
            XCTAssertEqual(u.params.x, Float(eye.rawValue))
            XCTAssertEqual(u.params.y, 0.8)
            XCTAssertEqual(u.lensCenter.x, layout[eye].lensCenterPixels.x)
            XCTAssertEqual(u.lensCenter.z, layout.pixelsPerTangent)
            XCTAssertEqual(u.bufferTangents, layout[eye].bufferTangents.shaderVector)
            XCTAssertEqual(u.rotation.columns.0, SIMD3(1, 0, 0))
        }
        let frame = VRFrameBuilder.distortionFrame(layout: layout, chromaticCorrection: false, bicubic: true, focusChart: false, brightness: 1)
        XCTAssertEqual(frame.chroma.w, 0)
        XCTAssertEqual(frame.output.z, 2556)
        XCTAssertEqual(frame.coefficients.x, 0.441)
        XCTAssertEqual(frame.options, SIMD4(1, 0, 0, 0))
        let chart = VRFrameBuilder.distortionFrame(layout: layout, chromaticCorrection: true, bicubic: false, focusChart: true, brightness: 1)
        XCTAssertEqual(chart.options, SIMD4(0, 1, 0, 0))
    }

    func testAutomaticResolutionSamplesTheLensAxisAboutOneAndAHalfTimes() {
        XCTAssertEqual(layout.centerSampling(resolution: 1024), 1.21, accuracy: 0.01)
        XCTAssertEqual(layout.centerSampling(resolution: 1280), 1.52, accuracy: 0.01)
        let automatic = PhoneVRSettings.EyeResolution.automatic.cap
        XCTAssertEqual(automatic.resolution, 1280)
        XCTAssertTrue(automatic.adaptive)
        XCTAssertLessThan(layout.centerSampling(resolution: 768), 1, "768² undersamples the panel at the lens axis")
    }

    // MARK: - Focus chart

    func testFocusChartLeavesTheCentreClear() {
        for x in stride(from: -19.5, through: 19.5, by: 1) {
            for y in stride(from: -19.5, through: 19.5, by: 1) {
                XCTAssertNil(VRFocusChart.value(at: SIMD2(Float(x), Float(y))))
            }
        }
        XCTAssertNil(VRFocusChart.value(at: SIMD2(VRFocusChart.extent + 0.5, 0)))
        XCTAssertNil(VRFocusChart.value(at: SIMD2(0, -VRFocusChart.extent - 0.5)))
    }

    func testFocusChartAlternatesSinglePixelLines() {
        let rows = stride(from: Float(-17.5), through: 17.5, by: 1)
        for x in stride(from: Float(20.5), through: 54.5, by: 1) {
            // Left and right of the centre: columns alternate, rows don't.
            let right = rows.map { VRFocusChart.value(at: SIMD2(x, $0)) }
            XCTAssertEqual(Set(right), [VRFocusChart.value(at: SIMD2(x, 0))])
            XCTAssertNotEqual(VRFocusChart.value(at: SIMD2(x, 0)), VRFocusChart.value(at: SIMD2(x + 1, 0)))
            XCTAssertNotEqual(VRFocusChart.value(at: SIMD2(-x, 0)), VRFocusChart.value(at: SIMD2(-x - 1, 0)))
            // Above and below: rows alternate.
            XCTAssertNotEqual(VRFocusChart.value(at: SIMD2(0, x)), VRFocusChart.value(at: SIMD2(0, x + 1)))
            XCTAssertNotEqual(VRFocusChart.value(at: SIMD2(5, -x)), VRFocusChart.value(at: SIMD2(5, -x - 1)))
        }
    }

    func testFocusChartCornersUseTwoPixelLines() {
        let row = stride(from: Float(20.5), through: 55.5, by: 1).map { VRFocusChart.value(at: SIMD2($0, 30.5)) ?? -1 }
        // Bottom right holds vertical lines two pixels wide.
        var runs: [Int] = []
        var previous: Float?
        for value in row {
            if value == previous {
                runs[runs.count - 1] += 1
            } else {
                runs.append(1)
            }
            previous = value
        }
        XCTAssertTrue(runs.dropFirst().dropLast().allSatisfy { $0 == 2 }, "\(runs)")
        // Top right holds horizontal ones, constant along a row.
        let topRight = Set(stride(from: Float(20.5), through: 55.5, by: 1).map { VRFocusChart.value(at: SIMD2($0, -30.5)) })
        XCTAssertEqual(topRight.count, 1)
    }

    func testFocusChartFitsInTheSharpCentreOfTheField() {
        for eye in VREye.allCases {
            let reach = VRFocusChart.extent * Float(2).squareRoot()
            XCTAssertLessThan(reach, layout[eye].visibleRadiusPixels / 4)
        }
    }

    func testReticleKeepsItsAngularSize() {
        let near = VRFrameBuilder.reticleUniforms(head: head, origin: head.position, direction: SIMD3(0, 0, -1), distance: 1, progress: 0.5, highlighted: true)
        let far = VRFrameBuilder.reticleUniforms(head: head, origin: head.position, direction: SIMD3(0, 0, -1), distance: 3, progress: 0, highlighted: false)
        XCTAssertEqual(far.model.columns.0.x / near.model.columns.0.x, 3, accuracy: 1e-4)
        XCTAssertEqual(near.params.x, 0.5)
        XCTAssertEqual(near.model.columns.3.z, -1, accuracy: 1e-5)
    }

    func testHeadLockedPanelFollowsTheHead() {
        let turned = VRPose(rotation: VRMath.rotationY(.pi / 2), position: SIMD3(0, 1.6, 0))
        let panel = VRFrameBuilder.headLocked(head: turned, offset: SIMD3(0, -0.3, -1.1), size: SIMD2(0.4, 0.2))
        // Turned to face world -X, the panel sits about 1.1 m to the left.
        XCTAssertEqual(panel.center.x, -1.1, accuracy: 1e-4)
        XCTAssertEqual(panel.center.y, 1.3, accuracy: 1e-4)
        XCTAssertNotNil(panel.hit(origin: turned.position, direction: simd_normalize(panel.center - turned.position)))
    }

    func testPassthroughHidesTheFloor() {
        let normal = VRFrameBuilder.instances(scene: .studio, reduced: false, time: 0, passthrough: false)
        let camera = VRFrameBuilder.instances(scene: .studio, reduced: false, time: 0, passthrough: true)
        XCTAssertEqual(camera.count, normal.count - 1)
        XCTAssertFalse(camera.contains { $0.uniforms.params.x == Float(VRMaterial.floorGrid.rawValue) })
    }

    func testInstancesTintByTheirObjectColor() {
        let ornament = VRSceneObject(mesh: .icosahedron, material: .lit, position: .zero, scale: SIMD3(repeating: 1), color: VRPalette.coral)
        let dimmed = SIMD4<Float>(0.5, 0.5, 0.5, 1)
        XCTAssertEqual(VRFrameBuilder.instance(ornament, time: 0).uniforms.tint, VRPalette.linear(VRPalette.coral))
        XCTAssertEqual(VRFrameBuilder.instance(ornament, time: 0, tint: dimmed).uniforms.tint, VRPalette.linear(VRPalette.coral) * dimmed)
        let hub = VRFrameBuilder.hubInstance(center: .zero, highlighted: true, time: 0).uniforms.tint
        XCTAssertEqual(hub, VRPalette.linear(VRPalette.teal))
    }
}
