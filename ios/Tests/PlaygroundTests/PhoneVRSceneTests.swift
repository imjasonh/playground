import XCTest
import simd
@testable import Playground

final class PhoneVRSceneTests: XCTestCase {
    // MARK: - Meshes

    func testVertexLayoutMatchesShaders() {
        XCTAssertEqual(MemoryLayout<VRSceneVertex>.size, 28)
        XCTAssertEqual(MemoryLayout<VRSceneVertex>.stride, 28)
        XCTAssertEqual(MemoryLayout<VRSceneVertex>.offset(of: \VRSceneVertex.nx), 12)
        XCTAssertEqual(MemoryLayout<VRSceneVertex>.offset(of: \VRSceneVertex.color), 24)
    }

    func testPalettePacksRedInTheLowByte() {
        XCTAssertEqual(VRPalette.rgba(0x112233), 0xFF33_2211)
        XCTAssertEqual(VRPalette.rgba(0x112233, alpha: 0x80), 0x8033_2211)
    }

    func testPaletteDecodesToLinearColor() {
        XCTAssertEqual(VRPalette.linear(VRPalette.white), SIMD4(1, 1, 1, 1))
        XCTAssertEqual(VRPalette.linear(VRPalette.rgba(0x000000)), SIMD4(0, 0, 0, 1))
        let gray = VRPalette.linear(VRPalette.rgba(0x808080, alpha: 0x80))
        XCTAssertEqual(gray.x, 0.2159, accuracy: 0.0005)
        XCTAssertEqual(gray.y, gray.x)
        XCTAssertEqual(gray.z, gray.x)
        XCTAssertEqual(gray.w, 128.0 / 255, accuracy: 1e-6)
        let coral = VRPalette.linear(VRPalette.coral)
        XCTAssertGreaterThan(coral.x, 5 * coral.y)
    }

    func testMeshesAreWhiteSoObjectsSetTheirColor() {
        for kind in VRMeshKind.allCases {
            XCTAssertTrue(VRMeshFactory.mesh(kind).vertices.allSatisfy { $0.color == VRPalette.white }, "\(kind)")
        }
    }

    func testEveryMeshIsWellFormed() {
        for kind in VRMeshKind.allCases {
            let mesh = VRMeshFactory.mesh(kind)
            XCTAssertFalse(mesh.indices.isEmpty, "\(kind)")
            XCTAssertEqual(mesh.indices.count % 3, 0, "\(kind)")
            XCTAssertLessThan(mesh.vertices.count, Int(UInt16.max), "\(kind)")
            XCTAssertTrue(mesh.indices.allSatisfy { Int($0) < mesh.vertices.count }, "\(kind)")
            for v in mesh.vertices {
                XCTAssertEqual(simd_length(v.normal), 1, accuracy: 1e-3, "\(kind)")
            }
            var k = 0
            while k < mesh.indices.count {
                let a = mesh.vertices[Int(mesh.indices[k])]
                let b = mesh.vertices[Int(mesh.indices[k + 1])]
                let c = mesh.vertices[Int(mesh.indices[k + 2])]
                let geometric = simd_cross(b.position - a.position, c.position - a.position)
                XCTAssertGreaterThanOrEqual(simd_dot(geometric, a.normal + b.normal + c.normal), 0, "\(kind) triangle \(k / 3) is wound against its normals")
                k += 3
            }
        }
    }

    func testSolidsFaceOutwardAndTheRoomFacesIn() {
        func facing(_ kind: VRMeshKind, center: SIMD3<Float>) -> [Float] {
            let mesh = VRMeshFactory.mesh(kind)
            var signs: [Float] = []
            var k = 0
            while k < mesh.indices.count {
                let a = mesh.vertices[Int(mesh.indices[k])].position
                let b = mesh.vertices[Int(mesh.indices[k + 1])].position
                let c = mesh.vertices[Int(mesh.indices[k + 2])].position
                signs.append(simd_dot(simd_cross(b - a, c - a), (a + b + c) / 3 - center))
                k += 3
            }
            return signs
        }
        for kind in [VRMeshKind.cube, .icosahedron, .sphere] {
            XCTAssertTrue(facing(kind, center: .zero).allSatisfy { $0 > 0 }, "\(kind)")
        }
        XCTAssertTrue(facing(.cylinder, center: SIMD3(0, 0.5, 0)).allSatisfy { $0 > 0 })
        XCTAssertTrue(facing(.room, center: SIMD3(0, 0.5, 0)).allSatisfy { $0 < 0 })
    }

    func testFloorFacesUp() {
        let floor = VRMeshFactory.mesh(.floor)
        let a = floor.vertices[Int(floor.indices[0])].position
        let b = floor.vertices[Int(floor.indices[1])].position
        let c = floor.vertices[Int(floor.indices[2])].position
        XCTAssertGreaterThan(simd_cross(b - a, c - a).y, 0)
    }

    // MARK: - Scene layout

    func testReducedStudioDropsObjects() {
        let full = VRSceneLayout.objects(for: .studio, reduced: false)
        let reduced = VRSceneLayout.objects(for: .studio, reduced: true)
        XCTAssertLessThan(reduced.count, full.count)
        XCTAssertEqual(full.first?.material, .floorGrid)
        XCTAssertEqual(VRSceneLayout.objects(for: .calibration, reduced: false).first?.material, .roomGrid)
        XCTAssertTrue(VRSceneLayout.objects(for: .minecraft, reduced: false).isEmpty)
        XCTAssertTrue(VRSceneLayout.objects(for: .minecraft, reduced: true).isEmpty)
    }

    func testSceneKindCyclesStudioCalibrationMinecraft() {
        XCTAssertEqual(VRSceneKind.studio.next, .calibration)
        XCTAssertEqual(VRSceneKind.calibration.next, .minecraft)
        XCTAssertEqual(VRSceneKind.minecraft.next, .studio)
        XCTAssertEqual(VRSceneKind.studio.next.menuTitle, "Calibrate lenses")
        XCTAssertEqual(VRSceneKind.calibration.next.menuTitle, "Minecraft")
        XCTAssertEqual(VRSceneKind.minecraft.next.menuTitle, "Studio")
    }

    func testPackLinearRoundTripsThroughTheShaderDecode() {
        XCTAssertEqual(VRPalette.linear(VRPalette.packLinear(SIMD3(1, 0, 0))), SIMD4(1, 0, 0, 1))
        XCTAssertEqual(VRPalette.linear(VRPalette.packLinear(SIMD3(0, 1, 0))), SIMD4(0, 1, 0, 1))
        XCTAssertEqual(VRPalette.linear(VRPalette.packLinear(SIMD3(repeating: 1))), SIMD4(1, 1, 1, 1))
        let grayLinear = VRPalette.linear(VRPalette.rgba(0x808080)).x
        let packedGray = VRPalette.packLinear(SIMD3(repeating: grayLinear))
        XCTAssertEqual(packedGray & 0xFF, 0x80)
        XCTAssertEqual((packedGray >> 8) & 0xFF, 0x80)
        XCTAssertEqual((packedGray >> 16) & 0xFF, 0x80)
    }

    func testBeaconOrbitsAtEarHeight() {
        for t in stride(from: 0.0, to: 30, by: 3.7) {
            let p = VRSceneLayout.beaconPosition(at: t)
            XCTAssertEqual(p.y, 1.55, accuracy: 1e-4)
            XCTAssertEqual(simd_length(SIMD2(p.x, p.z)), 2.2, accuracy: 1e-3)
        }
    }

    func testModelMatrixScalesThenRotatesThenTranslates() {
        let object = VRSceneObject(
            mesh: .cube, material: .lit, position: SIMD3(1, 2, 3), rotation: VRMath.rotationY(.pi / 2),
            scale: SIMD3(2, 1, 1), color: VRPalette.white
        )
        let p = object.modelMatrix(at: 0) * SIMD4<Float>(1, 0, 0, 1)
        XCTAssertEqual(p.x, 1, accuracy: 1e-5)
        XCTAssertEqual(p.y, 2, accuracy: 1e-5)
        XCTAssertEqual(p.z, 1, accuracy: 1e-5)
    }

    // MARK: - Panels

    func testPanelHitReturnsTextureCoordinates() {
        let head = VRPose(rotation: VRMath.identityRotation, position: SIMD3(0, 1.6, 0))
        let panel = VRPanelPlacement.inFront(of: head, distance: 1, drop: 0, size: SIMD2(0.6, 0.4))
        let hit = panel.hit(origin: head.position, direction: SIMD3(0, 0, -1))
        XCTAssertEqual(hit?.uv.x ?? -1, 0.5, accuracy: 1e-4)
        XCTAssertEqual(hit?.uv.y ?? -1, 0.5, accuracy: 1e-4)
        XCTAssertEqual(hit?.distance ?? -1, 1, accuracy: 1e-4)
        // Up and right on the panel are up and right in the texture's v-down space.
        let corner = panel.hit(origin: head.position, direction: simd_normalize(SIMD3(0.25, 0.15, -1)))
        XCTAssertGreaterThan(corner?.uv.x ?? 0, 0.5)
        XCTAssertLessThan(corner?.uv.y ?? 1, 0.5)
        XCTAssertNil(panel.hit(origin: SIMD3(0, 1.6, -2), direction: SIMD3(0, 0, 1)))
    }

    func testPanelButtonsStayInsideAndDontOverlap() {
        for buttons in [VRPanelLayouts.menuButtons, VRPanelLayouts.calibrationButtons, VRPanelLayouts.sceneSignButtons] {
            for (i, a) in buttons.enumerated() {
                XCTAssertGreaterThanOrEqual(a.frame.x, 0)
                XCTAssertGreaterThanOrEqual(a.frame.y, 0)
                XCTAssertLessThanOrEqual(a.frame.x + a.frame.width, 1)
                XCTAssertLessThanOrEqual(a.frame.y + a.frame.height, 1)
                for b in buttons[(i + 1)...] {
                    let overlaps = a.frame.x < b.frame.x + b.frame.width && b.frame.x < a.frame.x + a.frame.width
                        && a.frame.y < b.frame.y + b.frame.height && b.frame.y < a.frame.y + a.frame.height
                    XCTAssertFalse(overlaps, "\(a.target) overlaps \(b.target)")
                }
            }
        }
        XCTAssertEqual(VRPanelLayouts.menuButtons.count, VRMenuItem.allCases.count)
        XCTAssertEqual(VRPanelLayouts.sceneSignButtons.map(\.target), VRSceneKind.allCases.map { .sceneSign($0) })
    }

    func testSceneSignFacesTheOriginAndStandsOnAPost() {
        let placement = VRSceneLayout.sceneSignPlacement
        XCTAssertEqual(placement.size, VRPanelLayouts.sceneSignSize)
        let normal = placement.rotation.act(SIMD3(0, 0, 1))
        let towardOrigin = simd_normalize(SIMD3(-placement.center.x, 0, -placement.center.z))
        XCTAssertEqual(normal.x, towardOrigin.x, accuracy: 1e-5)
        XCTAssertEqual(normal.z, towardOrigin.z, accuracy: 1e-5)
        XCTAssertGreaterThan(placement.center.y, 1)
        XCTAssertLessThan(placement.center.x, 0)
        let studio = VRSceneLayout.objects(for: .studio, reduced: true)
        XCTAssertTrue(studio.contains { $0.mesh == .cylinder && abs($0.position.x - placement.center.x) < 1e-5 })
        XCTAssertTrue(studio.contains { $0.mesh == .cube && abs($0.position.y - placement.center.y) < 0.05 })
    }

    // MARK: - Experience

    private let ahead = VRPose(rotation: VRMath.identityRotation, position: SIMD3(0, 1.6, 0))

    private func lookingDown() -> VRPose {
        VRPose(rotation: VRMath.rotationX(VRMath.radians(-75)), position: SIMD3(0, 1.6, 0))
    }

    private func head(lookingAt point: SIMD3<Float>, from position: SIMD3<Float>) -> VRPose {
        VRPose(rotation: simd_quatf(from: SIMD3(0, 0, -1), to: simd_normalize(point - position)), position: position)
    }

    private func worldPoint(of target: VRGazeTarget, on placement: VRPanelPlacement, buttons: [VRPanelButton]) -> SIMD3<Float>? {
        guard let button = buttons.first(where: { $0.target == target }) else { return nil }
        let uv = button.frame.center
        let local = SIMD3((uv.x - 0.5) * placement.size.x, (0.5 - uv.y) * placement.size.y, 0)
        return placement.center + placement.rotation.act(local)
    }

    func testCountdownEndsWithARecenter() {
        var experience = VRExperience(profile: .standard, countdown: 1, passthroughAvailable: true, showStats: false)
        XCTAssertTrue(experience.isCountingDown)
        XCTAssertEqual(experience.handle(.tick(dt: 0.5, head: ahead)), [])
        XCTAssertNotNil(experience.state.countdownPlacement)
        XCTAssertNil(experience.gazeTarget(head: lookingDown()))
        let actions = experience.handle(.tick(dt: 0.6, head: ahead))
        XCTAssertTrue(actions.contains(.recenter))
        XCTAssertFalse(experience.isCountingDown)
    }

    func testAnyInputSkipsTheCountdown() {
        var tap = VRExperience(profile: .standard, countdown: 5, passthroughAvailable: true, showStats: false)
        XCTAssertTrue(tap.handle(.tap(target: nil, head: ahead)).contains(.recenter))
        var pad = VRExperience(profile: .standard, countdown: 5, passthroughAvailable: true, showStats: false)
        XCTAssertTrue(pad.handle(.controller(.b, target: nil, head: ahead)).contains(.recenter))
        XCTAssertFalse(pad.isCountingDown)
    }

    func testLookingDownAtTheHubOpensTheMenu() {
        var experience = VRExperience(profile: .standard, countdown: 0, passthroughAvailable: true, showStats: false)
        XCTAssertNil(experience.gazeTarget(head: ahead))
        XCTAssertEqual(experience.gazeTarget(head: lookingDown()), .menuHub)
        _ = experience.handle(.gazeSelected(.menuHub, head: lookingDown()))
        XCTAssertTrue(experience.state.menuOpen)
        guard let menu = experience.state.menuPlacement else { return XCTFail("menu should be placed") }
        // The menu opens ahead at the head's heading even though the head looked down.
        XCTAssertLessThan(menu.center.z, -0.5)
        XCTAssertNotEqual(experience.gazeTarget(head: lookingDown()), .menuHub)
    }

    func testEveryMenuButtonIsReachableByGaze() {
        var experience = VRExperience(profile: .standard, countdown: 0, passthroughAvailable: true, showStats: false)
        _ = experience.handle(.tap(target: nil, head: ahead))
        guard let menu = experience.state.menuPlacement else { return XCTFail("menu should be open") }
        for item in VRMenuItem.allCases {
            guard let point = worldPoint(of: .menu(item), on: menu, buttons: VRPanelLayouts.menuButtons) else {
                return XCTFail("no button for \(item)")
            }
            XCTAssertEqual(experience.gazeTarget(head: head(lookingAt: point, from: ahead.position)), .menu(item))
        }
        let exitHead = head(lookingAt: worldPoint(of: .menu(.exit), on: menu, buttons: VRPanelLayouts.menuButtons) ?? .zero, from: ahead.position)
        XCTAssertEqual(experience.handle(.gazeSelected(.menu(.exit), head: exitHead)), [.exit])
    }

    func testPassthroughNeedsTheCamera() {
        var experience = VRExperience(profile: .standard, countdown: 0, passthroughAvailable: false, showStats: false)
        XCTAssertEqual(experience.handle(.controller(.x, target: nil, head: ahead)), [])
        experience.setPassthroughAvailable(true)
        XCTAssertEqual(experience.handle(.controller(.x, target: nil, head: ahead)), [.passthroughChanged(true), .haptic])
        experience.setPassthroughAvailable(false)
        XCTAssertFalse(experience.state.passthrough)
    }

    func testCalibrationAdjustsTheProfile() {
        var experience = VRExperience(profile: .standard, countdown: 0, passthroughAvailable: true, showStats: false)
        _ = experience.handle(.tap(target: nil, head: ahead))
        XCTAssertEqual(experience.handle(.gazeSelected(.menu(.scene), head: ahead)), [.sceneChanged(.calibration), .haptic])
        XCTAssertNotNil(experience.state.calibrationPlacement)
        XCTAssertEqual(experience.handle(.controller(.dpadRight, target: nil, head: ahead)), [.profileChanged])
        XCTAssertEqual(experience.state.profile.distortionK1, 0.461, accuracy: 1e-5)
        _ = experience.handle(.controller(.dpadDown, target: nil, head: ahead))
        XCTAssertEqual(experience.state.selectedParameter, .k2)
        _ = experience.handle(.controller(.dpadLeft, target: nil, head: ahead))
        XCTAssertEqual(experience.state.profile.distortionK2, 0.136, accuracy: 1e-5)

        guard let panel = experience.state.calibrationPlacement,
              let plus = worldPoint(of: .calibrationStep(.interLensDistance, 1), on: panel, buttons: VRPanelLayouts.calibrationButtons)
        else { return XCTFail("calibration panel should have a + button for lens spacing") }
        let target = experience.gazeTarget(head: head(lookingAt: plus, from: ahead.position))
        XCTAssertEqual(target, .calibrationStep(.interLensDistance, 1))
        _ = experience.handle(.gazeSelected(.calibrationStep(.interLensDistance, 1), head: ahead))
        XCTAssertEqual(experience.state.profile.interLensDistance, 0.0644, accuracy: 1e-5)
        XCTAssertEqual(experience.handle(.controller(.b, target: nil, head: ahead)), [.sceneChanged(.studio), .haptic])
    }

    func testStudioSceneSignSelectsEachScene() {
        var experience = VRExperience(profile: .standard, countdown: 0, passthroughAvailable: true, showStats: false)
        let placement = VRSceneLayout.sceneSignPlacement
        XCTAssertNil(experience.gazeTarget(head: ahead))
        XCTAssertNotNil(experience.panelDistance(origin: ahead.position, direction: simd_normalize(placement.center - ahead.position)))
        for scene in VRSceneKind.allCases {
            guard let point = worldPoint(of: .sceneSign(scene), on: placement, buttons: VRPanelLayouts.sceneSignButtons) else {
                return XCTFail("no sign button for \(scene)")
            }
            let looking = head(lookingAt: point, from: ahead.position)
            XCTAssertEqual(experience.gazeTarget(head: looking), .sceneSign(scene))
            if scene == .studio {
                XCTAssertEqual(experience.handle(.gazeSelected(.sceneSign(scene), head: looking)), [])
                XCTAssertEqual(experience.state.scene, .studio)
            } else {
                XCTAssertEqual(experience.handle(.gazeSelected(.sceneSign(scene), head: looking)), [.sceneChanged(scene), .haptic])
                XCTAssertEqual(experience.state.scene, scene)
                XCTAssertEqual(experience.handle(.controller(.b, target: nil, head: looking)), [.sceneChanged(.studio), .haptic])
            }
        }
    }

    func testSceneMenuCyclesThroughMinecraft() {
        var experience = VRExperience(profile: .standard, countdown: 0, passthroughAvailable: true, showStats: false)
        _ = experience.handle(.tap(target: nil, head: ahead))
        XCTAssertEqual(experience.handle(.gazeSelected(.menu(.scene), head: ahead)), [.sceneChanged(.calibration), .haptic])
        _ = experience.handle(.tap(target: nil, head: ahead))
        XCTAssertEqual(experience.handle(.gazeSelected(.menu(.scene), head: ahead)), [.sceneChanged(.minecraft), .haptic])
        XCTAssertEqual(experience.state.scene, .minecraft)
        XCTAssertNil(experience.state.calibrationPlacement)
        XCTAssertEqual(experience.handle(.controller(.b, target: nil, head: ahead)), [.sceneChanged(.studio), .haptic])
        XCTAssertEqual(experience.state.scene, .studio)
    }

    func testCalibrationPanelLeavesTheViewAheadClear() {
        var experience = VRExperience(profile: .standard, countdown: 0, passthroughAvailable: true, showStats: false)
        _ = experience.handle(.tap(target: nil, head: ahead))
        _ = experience.handle(.gazeSelected(.menu(.scene), head: ahead))
        let forward = SIMD3<Float>(0, 0, -1)
        // Straight ahead is free for the target and the focus chart.
        XCTAssertNil(experience.panelDistance(origin: ahead.position, direction: forward))
        XCTAssertNil(experience.panelDistance(origin: ahead.position, direction: VRMath.rotationX(-VRMath.radians(5)).act(forward)))
        // A glance down reaches the panel.
        XCTAssertNotNil(experience.panelDistance(origin: ahead.position, direction: VRMath.rotationX(-VRMath.radians(20)).act(forward)))
    }

    func testCalibrationStopsAtTheRangeLimit() {
        var profile = VRViewerProfile.standard
        profile.redScale = 1.03
        let next = VRCalibrationParameter.redScale.adjusted(profile, steps: 1)
        XCTAssertEqual(next.redScale, 1.03, accuracy: 1e-6)
        XCTAssertEqual(VRCalibrationParameter.interLensDistance.formatted(.standard), "63.9 mm")
    }

    func testSnapTurnsFromShouldersAndDpad() {
        var experience = VRExperience(profile: .standard, countdown: 0, passthroughAvailable: true, showStats: false)
        XCTAssertEqual(experience.handle(.controller(.rightShoulder, target: nil, head: ahead)), [.snapTurn(VRMath.radians(30))])
        XCTAssertEqual(experience.handle(.controller(.dpadLeft, target: nil, head: ahead)), [.snapTurn(-VRMath.radians(30))])
    }

    // MARK: - Settings and statistics

    func testSettingsRoundTripAndFillDefaults() throws {
        var settings = PhoneVRSettings()
        settings.refreshRate = .hz60
        settings.profile.distortionK1 = 0.3
        settings.bicubicResampling = false
        let data = try JSONEncoder().encode(settings)
        XCTAssertEqual(try JSONDecoder().decode(PhoneVRSettings.self, from: data), settings)
        // Settings saved before a key existed load with its default.
        let partial = try JSONDecoder().decode(PhoneVRSettings.self, from: Data(#"{"timewarp": false}"#.utf8))
        XCTAssertFalse(partial.timewarp)
        XCTAssertTrue(partial.bicubicResampling)
        XCTAssertEqual(partial.profile, .standard)
        XCTAssertEqual(partial.mounting, .cameraLeft)
    }

    func testSettingsMapToGovernorCaps() {
        var settings = PhoneVRSettings()
        XCTAssertEqual(settings.governorConfiguration().maxRefreshRate, 120)
        XCTAssertEqual(settings.governorConfiguration().maxEyeResolution, 1280)
        XCTAssertTrue(settings.governorConfiguration().adaptiveResolution)
        settings.refreshRate = .hz60
        settings.eyeResolution = .r1280
        let configuration = settings.governorConfiguration()
        XCTAssertEqual(configuration.maxRefreshRate, 60)
        XCTAssertEqual(configuration.maxEyeResolution, 1280)
        XCTAssertFalse(configuration.adaptiveResolution)
    }

    func testHistogramQuantiles() {
        var histogram = VRLatencyHistogram()
        XCTAssertNil(histogram.quantile(0.5))
        for ms in 1...100 { histogram.record(milliseconds: Double(ms) / 10) }
        XCTAssertEqual(histogram.quantile(0.5) ?? 0, 5.0, accuracy: 0.11)
        XCTAssertEqual(histogram.quantile(0.95) ?? 0, 9.5, accuracy: 0.11)
    }

    func testFrameStatisticsCountMissedFrames() {
        var stats = VRFrameStatistics()
        let interval = 1.0 / 120
        var t = 0.0
        for i in 0..<10 {
            t += i == 5 ? interval * 3 : interval
            stats.recordFrame(presentationTime: t, expectedInterval: interval, cpuMilliseconds: 2, mode: i < 5 ? .sixDoF : .threeDoF, thermal: .fair, eyeResolution: 1024)
        }
        let summary = stats.summary(endedAt: Date(timeIntervalSince1970: 0), slips: 1, airPodsLatency: 0.08)
        XCTAssertEqual(summary.frames, 10)
        XCTAssertEqual(summary.missedFrames, 2)
        XCTAssertEqual(summary.sixDoFFraction, 0.5, accuracy: 1e-9)
        XCTAssertEqual(summary.hottestThermalLevel, VRThermalLevel.fair.rawValue)
        XCTAssertEqual(summary.airPodsLatencyMilliseconds ?? 0, 80, accuracy: 1e-6)
    }
}
