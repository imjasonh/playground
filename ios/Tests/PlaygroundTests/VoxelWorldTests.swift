import XCTest
import simd
@testable import Playground

final class VoxelGridTests: XCTestCase {
    func testKeyQuantizesByVoxelSize() {
        let grid = VoxelGrid(voxelSize: 0.1)
        XCTAssertEqual(grid.key(for: SIMD3(0.05, 0.05, 0.05)), VoxelKey(x: 0, y: 0, z: 0))
        XCTAssertEqual(grid.key(for: SIMD3(0.25, 0.05, 0.05)), VoxelKey(x: 2, y: 0, z: 0))
    }

    func testKeyFloorsNegativeCoordinates() {
        let grid = VoxelGrid(voxelSize: 0.1)
        XCTAssertEqual(grid.key(for: SIMD3(-0.05, -0.15, 0.05)), VoxelKey(x: -1, y: -2, z: 0))
    }

    func testCenterIsMiddleOfCell() {
        let grid = VoxelGrid(voxelSize: 0.1)
        let center = grid.center(of: VoxelKey(x: 0, y: -1, z: 2))
        XCTAssertEqual(center.x, 0.05, accuracy: 0.0001)
        XCTAssertEqual(center.y, -0.05, accuracy: 0.0001)
        XCTAssertEqual(center.z, 0.25, accuracy: 0.0001)
    }

    func testAddSampleCreatesThenUpdates() {
        var grid = VoxelGrid(voxelSize: 0.1)
        let point = SIMD3<Float>(0.05, 0.05, 0.05)

        let first = grid.addSample(worldPoint: point, color: SIMD3(1, 0, 0), maxVoxels: 10)
        XCTAssertEqual(first, .added(VoxelKey(x: 0, y: 0, z: 0)))
        XCTAssertEqual(grid.voxelCount, 1)

        let second = grid.addSample(worldPoint: point, color: SIMD3(0, 1, 0), maxVoxels: 10)
        XCTAssertEqual(second, .updated(VoxelKey(x: 0, y: 0, z: 0)))
        XCTAssertEqual(grid.voxelCount, 1)
    }

    func testColorConvergesTowardRepeatedSamples() {
        var grid = VoxelGrid(voxelSize: 0.1)
        let point = SIMD3<Float>(0.05, 0.05, 0.05)
        _ = grid.addSample(worldPoint: point, color: SIMD3(1, 0, 0), maxVoxels: 10)
        for _ in 0..<20 {
            _ = grid.addSample(worldPoint: point, color: SIMD3(0, 0, 1), maxVoxels: 10)
        }
        let color = grid.data(for: VoxelKey(x: 0, y: 0, z: 0))!.color
        XCTAssertGreaterThan(color.z, 0.9)
        XCTAssertLessThan(color.x, 0.1)
    }

    func testBudgetRejectsNewVoxelsButUpdatesExisting() {
        var grid = VoxelGrid(voxelSize: 0.1)
        XCTAssertEqual(
            grid.addSample(worldPoint: SIMD3(0.05, 0, 0), color: SIMD3(1, 1, 1), maxVoxels: 1),
            .added(VoxelKey(x: 0, y: 0, z: 0))
        )
        XCTAssertEqual(
            grid.addSample(worldPoint: SIMD3(0.95, 0, 0), color: SIMD3(1, 1, 1), maxVoxels: 1),
            .rejectedBudget
        )
        XCTAssertEqual(
            grid.addSample(worldPoint: SIMD3(0.05, 0, 0), color: SIMD3(0, 0, 0), maxVoxels: 1),
            .updated(VoxelKey(x: 0, y: 0, z: 0))
        )
    }

    func testInvalidPointsRejected() {
        var grid = VoxelGrid(voxelSize: 0.1)
        XCTAssertEqual(
            grid.addSample(worldPoint: SIMD3(.nan, 0, 0), color: SIMD3(1, 1, 1), maxVoxels: 10),
            .rejectedInvalid
        )
        XCTAssertEqual(
            grid.addSample(worldPoint: SIMD3(.infinity, 0, 0), color: SIMD3(1, 1, 1), maxVoxels: 10),
            .rejectedInvalid
        )
        XCTAssertEqual(grid.voxelCount, 0)
    }

    func testChunkKeyFloorsNegativeVoxels() {
        let grid = VoxelGrid(voxelSize: 0.1, chunkSize: 8)
        XCTAssertEqual(grid.chunkKey(for: VoxelKey(x: 0, y: 7, z: 8)), VoxelChunkKey(x: 0, y: 0, z: 1))
        XCTAssertEqual(grid.chunkKey(for: VoxelKey(x: -1, y: -8, z: -9)), VoxelChunkKey(x: -1, y: -1, z: -2))
    }

    func testFloorDiv() {
        XCTAssertEqual(VoxelGrid.floorDiv(7, 8), 0)
        XCTAssertEqual(VoxelGrid.floorDiv(8, 8), 1)
        XCTAssertEqual(VoxelGrid.floorDiv(-1, 8), -1)
        XCTAssertEqual(VoxelGrid.floorDiv(-8, 8), -1)
        XCTAssertEqual(VoxelGrid.floorDiv(-9, 8), -2)
    }

    func testAffectedChunksIncludesOccupiedNeighborChunk() {
        var grid = VoxelGrid(voxelSize: 0.1, chunkSize: 8)
        // Voxel at x=8 lives in chunk x=1; its neighbor at x=7 is chunk x=0.
        _ = grid.addSample(worldPoint: SIMD3(0.75, 0.05, 0.05), color: SIMD3(1, 1, 1), maxVoxels: 10)
        _ = grid.addSample(worldPoint: SIMD3(0.85, 0.05, 0.05), color: SIMD3(1, 1, 1), maxVoxels: 10)

        let affected = grid.affectedChunks(around: VoxelKey(x: 8, y: 0, z: 0))
        XCTAssertTrue(affected.contains(VoxelChunkKey(x: 1, y: 0, z: 0)))
        XCTAssertTrue(affected.contains(VoxelChunkKey(x: 0, y: 0, z: 0)))
    }

    func testAffectedChunksInteriorVoxelIsOnlyItsOwnChunk() {
        var grid = VoxelGrid(voxelSize: 0.1, chunkSize: 8)
        _ = grid.addSample(worldPoint: SIMD3(0.35, 0.35, 0.35), color: SIMD3(1, 1, 1), maxVoxels: 10)
        let affected = grid.affectedChunks(around: VoxelKey(x: 3, y: 3, z: 3))
        XCTAssertEqual(affected, [VoxelChunkKey(x: 0, y: 0, z: 0)])
    }

    func testRemoveAllClearsEverything() {
        var grid = VoxelGrid(voxelSize: 0.1)
        _ = grid.addSample(worldPoint: SIMD3(0.05, 0, 0), color: SIMD3(1, 1, 1), maxVoxels: 10)
        grid.removeAll()
        XCTAssertEqual(grid.voxelCount, 0)
        XCTAssertFalse(grid.isOccupied(VoxelKey(x: 0, y: 0, z: 0)))
    }

    func testRepeatedMissesCarveVoxelAway() {
        var grid = VoxelGrid(voxelSize: 0.1)
        let key = VoxelKey(x: 0, y: 0, z: 0)
        _ = grid.addSample(worldPoint: SIMD3(0.05, 0.05, 0.05), color: SIMD3(1, 1, 1), maxVoxels: 10)

        for _ in 1..<VoxelData.removalMissThreshold {
            XCTAssertFalse(grid.registerMiss(at: key))
            XCTAssertTrue(grid.isOccupied(key))
        }
        XCTAssertTrue(grid.registerMiss(at: key))
        XCTAssertFalse(grid.isOccupied(key))
        XCTAssertEqual(grid.voxelCount, 0)
    }

    func testConfirmationResetsMisses() {
        var grid = VoxelGrid(voxelSize: 0.1)
        let key = VoxelKey(x: 0, y: 0, z: 0)
        _ = grid.addSample(worldPoint: SIMD3(0.05, 0.05, 0.05), color: SIMD3(1, 1, 1), maxVoxels: 10)

        for _ in 1..<VoxelData.removalMissThreshold {
            XCTAssertFalse(grid.registerMiss(at: key))
        }
        grid.registerConfirmation(at: key)
        // The counter restarted, so the same number of misses again still
        // shouldn't remove it until the threshold is re-reached.
        for _ in 1..<VoxelData.removalMissThreshold {
            XCTAssertFalse(grid.registerMiss(at: key))
        }
        XCTAssertTrue(grid.isOccupied(key))
    }

    func testAddSampleResetsMisses() {
        var grid = VoxelGrid(voxelSize: 0.1)
        let key = VoxelKey(x: 0, y: 0, z: 0)
        let point = SIMD3<Float>(0.05, 0.05, 0.05)
        _ = grid.addSample(worldPoint: point, color: SIMD3(1, 1, 1), maxVoxels: 10)

        for _ in 1..<VoxelData.removalMissThreshold {
            XCTAssertFalse(grid.registerMiss(at: key))
        }
        _ = grid.addSample(worldPoint: point, color: SIMD3(1, 1, 1), maxVoxels: 10)
        XCTAssertEqual(grid.data(for: key)?.missCount, 0)
    }

    func testCarvingFreesBudgetForNewVoxels() {
        var grid = VoxelGrid(voxelSize: 0.1)
        let key = VoxelKey(x: 0, y: 0, z: 0)
        _ = grid.addSample(worldPoint: SIMD3(0.05, 0, 0), color: SIMD3(1, 1, 1), maxVoxels: 1)

        for _ in 0..<VoxelData.removalMissThreshold {
            _ = grid.registerMiss(at: key)
        }
        XCTAssertEqual(grid.voxelCount, 0)
        XCTAssertEqual(
            grid.addSample(worldPoint: SIMD3(0.95, 0, 0), color: SIMD3(1, 1, 1), maxVoxels: 1),
            .added(VoxelKey(x: 9, y: 0, z: 0))
        )
    }

    func testMissOnMissingVoxelIsHarmless() {
        var grid = VoxelGrid(voxelSize: 0.1)
        XCTAssertFalse(grid.registerMiss(at: VoxelKey(x: 5, y: 5, z: 5)))
        XCTAssertEqual(grid.voxelCount, 0)
    }
}

final class VoxelCarverTests: XCTestCase {
    private let voxelSize: Float = 0.25

    func testSurfaceAtVoxelDepthConfirms() {
        XCTAssertEqual(
            VoxelCarver.classify(voxelDepth: 2.0, observedDepth: 2.1, voxelSize: voxelSize),
            .confirmed
        )
        XCTAssertEqual(
            VoxelCarver.classify(voxelDepth: 2.0, observedDepth: 1.9, voxelSize: voxelSize),
            .confirmed
        )
    }

    func testSeeingWellPastVoxelIsFreeSpace() {
        XCTAssertEqual(
            VoxelCarver.classify(voxelDepth: 1.0, observedDepth: 3.0, voxelSize: voxelSize),
            .freeSpace
        )
    }

    func testOccludedVoxelIsUnknown() {
        // Something nearer blocks the view — no evidence about the voxel.
        XCTAssertEqual(
            VoxelCarver.classify(voxelDepth: 3.0, observedDepth: 1.0, voxelSize: voxelSize),
            .unknown
        )
    }

    func testMarginScalesWithVoxelSize() {
        // Just inside the margin → confirmed; just past it → free space.
        let margin = VoxelCarver.margin(voxelSize: voxelSize)
        XCTAssertEqual(
            VoxelCarver.classify(
                voxelDepth: 1.0,
                observedDepth: 1.0 + margin - 0.01,
                voxelSize: voxelSize
            ),
            .confirmed
        )
        XCTAssertEqual(
            VoxelCarver.classify(
                voxelDepth: 1.0,
                observedDepth: 1.0 + margin + 0.01,
                voxelSize: voxelSize
            ),
            .freeSpace
        )
    }

    func testInvalidDepthsAreUnknown() {
        XCTAssertEqual(
            VoxelCarver.classify(voxelDepth: 1.0, observedDepth: .nan, voxelSize: voxelSize),
            .unknown
        )
        XCTAssertEqual(
            VoxelCarver.classify(voxelDepth: 1.0, observedDepth: 0, voxelSize: voxelSize),
            .unknown
        )
        XCTAssertEqual(
            VoxelCarver.classify(voxelDepth: -1, observedDepth: 2, voxelSize: voxelSize),
            .unknown
        )
    }
}

final class VoxelPaletteTests: XCTestCase {
    func testPaletteColorsMapToThemselves() {
        for color in VoxelPalette.colors {
            XCTAssertEqual(VoxelPalette.quantize(color), color)
        }
    }

    func testQuantizeAlwaysReturnsPaletteMember() {
        let inputs: [SIMD3<Float>] = [
            SIMD3(0.31, 0.42, 0.53),
            SIMD3(0, 0, 0),
            SIMD3(1, 1, 1),
            SIMD3(0.99, 0.01, 0.5),
        ]
        for input in inputs {
            let output = VoxelPalette.quantize(input)
            XCTAssertTrue(VoxelPalette.colors.contains(output))
        }
    }

    func testGreenishInputSnapsToGreenishBlock() {
        let output = VoxelPalette.quantize(SIMD3(0.35, 0.6, 0.25))
        XCTAssertGreaterThan(output.y, output.x)
        XCTAssertGreaterThan(output.y, output.z)
    }

    func testNearBlackSnapsToBlack() {
        let output = VoxelPalette.quantize(SIMD3(0.05, 0.06, 0.08))
        XCTAssertEqual(output, SIMD3(0.11, 0.11, 0.13))
    }

    func testDistanceWeightsFavorGreenAccuracy() {
        let base = SIMD3<Float>(0.5, 0.5, 0.5)
        let greenOff = VoxelPalette.distanceSquared(base, SIMD3(0.5, 0.6, 0.5))
        let blueOff = VoxelPalette.distanceSquared(base, SIMD3(0.5, 0.5, 0.6))
        XCTAssertGreaterThan(greenOff, blueOff)
    }
}

final class VoxelSizeMappingTests: XCTestCase {
    func testEndpointsHitMinAndMax() {
        XCTAssertEqual(VoxelSizeMapping.size(sliderValue: 0), VoxelSizeMapping.minimumSize, accuracy: 0.0001)
        XCTAssertEqual(VoxelSizeMapping.size(sliderValue: 1), VoxelSizeMapping.maximumSize, accuracy: 0.0001)
    }

    func testRoundTrip() {
        for slider in stride(from: 0.0, through: 1.0, by: 0.25) {
            let size = VoxelSizeMapping.size(sliderValue: slider)
            XCTAssertEqual(VoxelSizeMapping.sliderValue(for: size), slider, accuracy: 0.001)
        }
    }

    func testMappingIsMonotonic() {
        let small = VoxelSizeMapping.size(sliderValue: 0.2)
        let large = VoxelSizeMapping.size(sliderValue: 0.8)
        XCTAssertLessThan(small, large)
    }

    func testDefaultSizeIsInRange() {
        XCTAssertGreaterThanOrEqual(VoxelSizeMapping.defaultSize, VoxelSizeMapping.minimumSize)
        XCTAssertLessThanOrEqual(VoxelSizeMapping.defaultSize, VoxelSizeMapping.maximumSize)
    }

    func testLabels() {
        XCTAssertEqual(VoxelSizeMapping.label(for: 0.1), "10 cm")
        XCTAssertEqual(VoxelSizeMapping.label(for: 0.25), "25 cm")
        XCTAssertEqual(VoxelSizeMapping.label(for: 0.5), "50 cm")
        XCTAssertEqual(VoxelSizeMapping.label(for: 0.123), "12.3 cm")
    }

    func testFloorIsChunky() {
        // The sensor can't support crisp small voxels; keep the floor ≥ 10 cm.
        XCTAssertGreaterThanOrEqual(VoxelSizeMapping.minimumSize, 0.10)
    }
}

final class VoxelMesherTests: XCTestCase {
    private func makeVoxels(_ keys: [VoxelKey]) -> [VoxelKey: VoxelData] {
        var voxels: [VoxelKey: VoxelData] = [:]
        for key in keys {
            voxels[key] = VoxelData(color: SIMD3(0.5, 0.5, 0.5))
        }
        return voxels
    }

    func testSingleVoxelEmitsSixFaces() {
        let voxels = makeVoxels([VoxelKey(x: 0, y: 0, z: 0)])
        let mesh = VoxelMesher.mesh(voxels: voxels, voxelSize: 0.1) { voxels[$0] != nil }

        XCTAssertEqual(mesh.faceCount, 6)
        XCTAssertEqual(mesh.positions.count, 24)
        XCTAssertEqual(mesh.normals.count, 24)
        XCTAssertEqual(mesh.colors.count, 24)
        XCTAssertEqual(mesh.indices.count, 36)
    }

    func testAdjacentVoxelsCullSharedFaces() {
        let voxels = makeVoxels([
            VoxelKey(x: 0, y: 0, z: 0),
            VoxelKey(x: 1, y: 0, z: 0),
        ])
        let mesh = VoxelMesher.mesh(voxels: voxels, voxelSize: 0.1) { voxels[$0] != nil }
        // 12 faces total minus the 2 shared interior faces.
        XCTAssertEqual(mesh.faceCount, 10)
    }

    func testOccupancyAcrossChunkBoundaryCullsFace() {
        // Only the single voxel is meshed, but its +x neighbor (in another
        // chunk) is reported occupied — that face must be culled.
        let voxels = makeVoxels([VoxelKey(x: 7, y: 0, z: 0)])
        let mesh = VoxelMesher.mesh(voxels: voxels, voxelSize: 0.1) { key in
            voxels[key] != nil || key == VoxelKey(x: 8, y: 0, z: 0)
        }
        XCTAssertEqual(mesh.faceCount, 5)
    }

    func testVertexPositionsSpanVoxelSize() {
        let voxels = makeVoxels([VoxelKey(x: 2, y: 0, z: 0)])
        let mesh = VoxelMesher.mesh(voxels: voxels, voxelSize: 0.5) { voxels[$0] != nil }

        let xs = mesh.positions.map(\.x)
        XCTAssertEqual(xs.min()!, 1.0, accuracy: 0.0001)
        XCTAssertEqual(xs.max()!, 1.5, accuracy: 0.0001)
    }

    func testFaceShadingBakedIntoVertexColors() {
        let voxels = makeVoxels([VoxelKey(x: 0, y: 0, z: 0)])
        let mesh = VoxelMesher.mesh(voxels: voxels, voxelSize: 0.1) { voxels[$0] != nil }

        var topColor: SIMD4<Float>?
        var bottomColor: SIMD4<Float>?
        for (index, normal) in mesh.normals.enumerated() {
            if normal.y > 0.5 { topColor = mesh.colors[index] }
            if normal.y < -0.5 { bottomColor = mesh.colors[index] }
        }
        XCTAssertNotNil(topColor)
        XCTAssertNotNil(bottomColor)
        XCTAssertGreaterThan(topColor!.x, bottomColor!.x)
        XCTAssertEqual(topColor!.w, 1)
    }

    func testNormalsAreUnitLength() {
        for face in VoxelMesher.faces {
            XCTAssertEqual(simd_length(face.normal), 1, accuracy: 0.0001)
        }
    }

    func testEmptyInputProducesEmptyMesh() {
        let mesh = VoxelMesher.mesh(voxels: [:], voxelSize: 0.1) { _ in false }
        XCTAssertTrue(mesh.isEmpty)
    }
}

final class VoxelProjectionTests: XCTestCase {
    private let intrinsics = simd_float3x3(columns: (
        SIMD3<Float>(100, 0, 0),
        SIMD3<Float>(0, 100, 0),
        SIMD3<Float>(50, 50, 1)
    ))

    func testCenterPixelUnprojectsAlongViewAxis() {
        let world = VoxelProjection.worldPoint(
            pixel: SIMD2(50, 50),
            depthMeters: 2,
            intrinsics: intrinsics,
            cameraTransform: matrix_identity_float4x4
        )
        XCTAssertNotNil(world)
        XCTAssertEqual(world!.x, 0, accuracy: 0.0001)
        XCTAssertEqual(world!.y, 0, accuracy: 0.0001)
        XCTAssertEqual(world!.z, -2, accuracy: 0.0001)
    }

    func testPixelBelowCenterMapsToNegativeWorldY() {
        let world = VoxelProjection.worldPoint(
            pixel: SIMD2(50, 100),
            depthMeters: 1,
            intrinsics: intrinsics,
            cameraTransform: matrix_identity_float4x4
        )!
        // Image y grows downward; ARKit camera +y is up.
        XCTAssertLessThan(world.y, 0)
        XCTAssertEqual(world.y, -0.5, accuracy: 0.0001)
    }

    func testCameraTranslationShiftsWorldPoint() {
        var transform = matrix_identity_float4x4
        transform.columns.3 = SIMD4<Float>(1, 2, 3, 1)
        let world = VoxelProjection.worldPoint(
            pixel: SIMD2(50, 50),
            depthMeters: 2,
            intrinsics: intrinsics,
            cameraTransform: transform
        )!
        XCTAssertEqual(world.x, 1, accuracy: 0.0001)
        XCTAssertEqual(world.y, 2, accuracy: 0.0001)
        XCTAssertEqual(world.z, 1, accuracy: 0.0001)
    }

    func testProjectionRoundTrip() {
        var transform = matrix_identity_float4x4
        transform.columns.3 = SIMD4<Float>(0.3, -0.2, 0.5, 1)

        let pixel = SIMD2<Float>(72, 31)
        let depth: Float = 1.7
        let world = VoxelProjection.worldPoint(
            pixel: pixel,
            depthMeters: depth,
            intrinsics: intrinsics,
            cameraTransform: transform
        )!
        let projected = VoxelProjection.pixel(
            worldPoint: world,
            intrinsics: intrinsics,
            cameraTransform: transform
        )
        XCTAssertNotNil(projected)
        XCTAssertEqual(projected!.pixel.x, pixel.x, accuracy: 0.01)
        XCTAssertEqual(projected!.pixel.y, pixel.y, accuracy: 0.01)
        XCTAssertEqual(projected!.depthMeters, depth, accuracy: 0.001)
    }

    func testPointBehindCameraIsNil() {
        let behind = VoxelProjection.pixel(
            worldPoint: SIMD3(0, 0, 5),
            intrinsics: intrinsics,
            cameraTransform: matrix_identity_float4x4
        )
        XCTAssertNil(behind)
    }

    func testInvalidDepthIsNil() {
        XCTAssertNil(VoxelProjection.worldPoint(
            pixel: SIMD2(50, 50),
            depthMeters: 0,
            intrinsics: intrinsics,
            cameraTransform: matrix_identity_float4x4
        ))
        XCTAssertNil(VoxelProjection.worldPoint(
            pixel: SIMD2(50, 50),
            depthMeters: .nan,
            intrinsics: intrinsics,
            cameraTransform: matrix_identity_float4x4
        ))
    }
}

final class VoxelColorConversionTests: XCTestCase {
    func testNeutralGray() {
        let rgb = VoxelColorConversion.rgb(y: 128, cb: 128, cr: 128)
        XCTAssertEqual(rgb.x, 0.5, accuracy: 0.01)
        XCTAssertEqual(rgb.y, 0.5, accuracy: 0.01)
        XCTAssertEqual(rgb.z, 0.5, accuracy: 0.01)
    }

    func testFullRangeBlackAndWhite() {
        let black = VoxelColorConversion.rgb(y: 0, cb: 128, cr: 128)
        XCTAssertEqual(black, SIMD3<Float>(0, 0, 0))
        let white = VoxelColorConversion.rgb(y: 255, cb: 128, cr: 128)
        XCTAssertEqual(white.x, 1, accuracy: 0.01)
        XCTAssertEqual(white.y, 1, accuracy: 0.01)
        XCTAssertEqual(white.z, 1, accuracy: 0.01)
    }

    func testHighCrLeansRed() {
        let rgb = VoxelColorConversion.rgb(y: 128, cb: 128, cr: 255)
        XCTAssertGreaterThan(rgb.x, rgb.y)
        XCTAssertGreaterThan(rgb.x, rgb.z)
    }

    func testHighCbLeansBlue() {
        let rgb = VoxelColorConversion.rgb(y: 128, cb: 255, cr: 128)
        XCTAssertGreaterThan(rgb.z, rgb.x)
        XCTAssertGreaterThan(rgb.z, rgb.y)
    }

    func testOutputStaysClamped() {
        let rgb = VoxelColorConversion.rgb(y: 255, cb: 255, cr: 255)
        XCTAssertLessThanOrEqual(simd_reduce_max(rgb), 1)
        XCTAssertGreaterThanOrEqual(simd_reduce_min(rgb), 0)
    }
}
