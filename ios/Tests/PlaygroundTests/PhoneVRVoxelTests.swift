import XCTest
import simd
@testable import Playground

final class PhoneVRVoxelTests: XCTestCase {
    func testTorchIsFullNearbyAndBlackAtRange() {
        XCTAssertEqual(VRTorchLight.attenuation(distance: 0), 1)
        XCTAssertEqual(VRTorchLight.attenuation(distance: VRTorchLight.innerMeters), 1)
        XCTAssertEqual(VRTorchLight.attenuation(distance: VRTorchLight.outerMeters), 0)
        XCTAssertEqual(VRTorchLight.attenuation(distance: 10), 0)
        let mid = (VRTorchLight.innerMeters + VRTorchLight.outerMeters) / 2
        XCTAssertEqual(VRTorchLight.attenuation(distance: mid), 0.25, accuracy: 1e-5)
    }

    func testTorchFalloffIsSmoothNotPixelated() {
        var previous = VRTorchLight.attenuation(distance: VRTorchLight.innerMeters)
        for step in 1...20 {
            let distance = VRTorchLight.innerMeters + Float(step) / 20 * (VRTorchLight.outerMeters - VRTorchLight.innerMeters)
            let next = VRTorchLight.attenuation(distance: distance)
            XCTAssertLessThan(next, previous)
            previous = next
        }
    }

    func testVoxelGeometryKeepsWorldPositions() {
        var grid = VoxelGrid(voxelSize: 0.1)
        _ = grid.addSample(worldPoint: SIMD3(0.05, 0.05, -1.05), color: SIMD3(1, 1, 1), maxVoxels: 10)
        let key = grid.key(for: SIMD3(0.05, 0.05, -1.05))
        let mesh = VoxelMesher.mesh(
            voxels: grid.voxels(in: grid.chunkKey(for: key)),
            voxelSize: 0.1,
            isOccupied: { grid.isOccupied($0) }
        )
        XCTAssertEqual(mesh.faceCount, 6)
        for p in mesh.positions {
            XCTAssertGreaterThanOrEqual(p.x, 0)
            XCTAssertLessThanOrEqual(p.x, 0.1)
            XCTAssertGreaterThanOrEqual(p.z, -1.1)
            XCTAssertLessThanOrEqual(p.z, -1.0)
        }
        let vertices = VRVoxelGeometry.sceneVertices(from: mesh)
        XCTAssertEqual(vertices.count, mesh.positions.count)
        XCTAssertTrue(vertices.allSatisfy { $0.color >> 24 == 255 })
    }

    func testPaletteSignatureIgnoresSubThresholdColorDrift() {
        var grid = VoxelGrid(voxelSize: 0.1)
        let point = SIMD3<Float>(0.05, 0.05, 0.05)
        let snow = SIMD3<Float>(0.97, 0.99, 0.99)
        _ = grid.addSample(worldPoint: point, color: snow, maxVoxels: 10)
        let chunk = grid.chunkKey(for: grid.key(for: point))
        let first = VRVoxelWorld.signature(of: grid.voxels(in: chunk))
        _ = grid.addSample(worldPoint: point, color: snow * 0.98, maxVoxels: 10)
        let second = VRVoxelWorld.signature(of: grid.voxels(in: chunk))
        XCTAssertEqual(first, second)

        for _ in 0..<80 {
            _ = grid.addSample(worldPoint: point, color: SIMD3(0.11, 0.11, 0.13), maxVoxels: 10)
        }
        let third = VRVoxelWorld.signature(of: grid.voxels(in: chunk))
        XCTAssertNotEqual(first, third)
    }

    func testWorldVoxelsStayRigidAcrossRecenter() {
        let worldPoint = SIMD3<Float>(0, 0, -2)
        var play = VRPlaySpace()
        XCTAssertEqual(play.sceneFromWorld.transformPoint(worldPoint), worldPoint)

        play.recenter(head: VRPose(rotation: VRMath.rotationY(.pi / 2), position: SIMD3(0, 1.6, 0)))
        let scene = play.sceneFromWorld.transformPoint(worldPoint)
        let back = play.worldFromScene.transformPoint(scene)
        XCTAssertEqual(back.x, worldPoint.x, accuracy: 1e-5)
        XCTAssertEqual(back.y, worldPoint.y, accuracy: 1e-5)
        XCTAssertEqual(back.z, worldPoint.z, accuracy: 1e-5)
        XCTAssertNotEqual(scene, worldPoint)
    }
}
