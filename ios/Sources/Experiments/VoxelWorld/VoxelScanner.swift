import CoreVideo
import Foundation
import simd

/// Folds one camera frame into a `VoxelGrid`: LiDAR depth (or sparse
/// feature points) unprojected into world space, colored from the image.
///
/// Voxel Eyes and Phone VR Minecraft share this so they agree on which
/// samples become voxels. Rendering after this step is the experiment's:
/// Voxel Eyes pixelizes the far field; Phone VR fades it to black.
enum VoxelScanner {
    /// Depth samples at or below this are not a surface.
    static let minimumDepth: Float = 0.05
    /// Depth-map sampling stride (256×192 map → ~12k samples per tick).
    static let depthStride = 2
    /// Feature-point cap on devices without scene depth.
    static let maxFeaturePoints = 2048
    /// ARKit `ARConfidenceLevel.medium` raw value. Samples below this are
    /// skipped when a confidence map is present.
    static let mediumConfidence: UInt8 = 1

    struct Result: Equatable {
        var structural: Set<VoxelChunkKey>
        var color: Set<VoxelChunkKey>
        var budgetHit: Bool
    }

    /// Integrates `capturedImage` (420f YCbCr) into `grid`. Locks the pixel
    /// buffers for the duration of the call.
    static func integrate(
        grid: inout VoxelGrid,
        intrinsics: simd_float3x3,
        cameraTransform: simd_float4x4,
        capturedImage: CVPixelBuffer,
        depthMap: CVPixelBuffer?,
        confidenceMap: CVPixelBuffer?,
        featurePoints: [SIMD3<Float>]?,
        maxVoxels: Int,
        maxDepth: Float
    ) -> Result {
        var structural = Set<VoxelChunkKey>()
        var color = Set<VoxelChunkKey>()
        var budgetHit = false

        CVPixelBufferLockBaseAddress(capturedImage, .readOnly)
        defer { CVPixelBufferUnlockBaseAddress(capturedImage, .readOnly) }

        guard
            CVPixelBufferGetPlaneCount(capturedImage) >= 2,
            let lumaBaseRaw = CVPixelBufferGetBaseAddressOfPlane(capturedImage, 0),
            let chromaBaseRaw = CVPixelBufferGetBaseAddressOfPlane(capturedImage, 1)
        else {
            return Result(structural: structural, color: color, budgetHit: budgetHit)
        }
        let luma = lumaBaseRaw.assumingMemoryBound(to: UInt8.self)
        let chroma = chromaBaseRaw.assumingMemoryBound(to: UInt8.self)
        let lumaBytesPerRow = CVPixelBufferGetBytesPerRowOfPlane(capturedImage, 0)
        let chromaBytesPerRow = CVPixelBufferGetBytesPerRowOfPlane(capturedImage, 1)
        let imageWidth = CVPixelBufferGetWidthOfPlane(capturedImage, 0)
        let imageHeight = CVPixelBufferGetHeightOfPlane(capturedImage, 0)
        let chromaWidth = CVPixelBufferGetWidthOfPlane(capturedImage, 1)
        let chromaHeight = CVPixelBufferGetHeightOfPlane(capturedImage, 1)

        func sampleColor(imageX: Int, imageY: Int) -> SIMD3<Float>? {
            guard imageX >= 0, imageX < imageWidth, imageY >= 0, imageY < imageHeight else {
                return nil
            }
            let y = luma[imageY * lumaBytesPerRow + imageX]
            let cx = min(imageX / 2, chromaWidth - 1)
            let cy = min(imageY / 2, chromaHeight - 1)
            let cb = chroma[cy * chromaBytesPerRow + cx * 2]
            let cr = chroma[cy * chromaBytesPerRow + cx * 2 + 1]
            return VoxelColorConversion.rgb(y: y, cb: cb, cr: cr)
        }

        func record(_ result: VoxelGrid.AddResult) {
            switch result {
            case .added(let key):
                structural.formUnion(grid.affectedChunks(around: key))
            case .updated(let key):
                color.insert(grid.chunkKey(for: key))
            case .rejectedBudget:
                budgetHit = true
            case .rejectedInvalid:
                break
            }
        }

        if let depthMap {
            CVPixelBufferLockBaseAddress(depthMap, .readOnly)
            if let confidenceMap {
                CVPixelBufferLockBaseAddress(confidenceMap, .readOnly)
            }
            defer {
                if let confidenceMap {
                    CVPixelBufferUnlockBaseAddress(confidenceMap, .readOnly)
                }
                CVPixelBufferUnlockBaseAddress(depthMap, .readOnly)
            }

            guard let depthBaseRaw = CVPixelBufferGetBaseAddress(depthMap) else {
                return Result(structural: structural, color: color, budgetHit: budgetHit)
            }
            let depthWidth = CVPixelBufferGetWidth(depthMap)
            let depthHeight = CVPixelBufferGetHeight(depthMap)
            let depthBytesPerRow = CVPixelBufferGetBytesPerRow(depthMap)

            var confidenceBase: UnsafePointer<UInt8>?
            var confidenceBytesPerRow = 0
            if let confidenceMap,
               CVPixelBufferGetWidth(confidenceMap) == depthWidth,
               CVPixelBufferGetHeight(confidenceMap) == depthHeight,
               let base = CVPixelBufferGetBaseAddress(confidenceMap) {
                confidenceBase = UnsafePointer(base.assumingMemoryBound(to: UInt8.self))
                confidenceBytesPerRow = CVPixelBufferGetBytesPerRow(confidenceMap)
            }

            let scaleX = Float(imageWidth) / Float(depthWidth)
            let scaleY = Float(imageHeight) / Float(depthHeight)

            for depthY in stride(from: 0, to: depthHeight, by: depthStride) {
                let depthRow = (depthBaseRaw + depthY * depthBytesPerRow)
                    .assumingMemoryBound(to: Float32.self)
                for depthX in stride(from: 0, to: depthWidth, by: depthStride) {
                    let depth = depthRow[depthX]
                    guard depth.isFinite,
                          depth > minimumDepth,
                          depth <= maxDepth else { continue }

                    if let confidenceBase {
                        let confidence = confidenceBase[depthY * confidenceBytesPerRow + depthX]
                        guard confidence >= mediumConfidence else { continue }
                    }

                    let pixelX = (Float(depthX) + 0.5) * scaleX
                    let pixelY = (Float(depthY) + 0.5) * scaleY
                    guard let sample = sampleColor(imageX: Int(pixelX), imageY: Int(pixelY)) else { continue }
                    guard let world = VoxelProjection.worldPoint(
                        pixel: SIMD2<Float>(pixelX, pixelY),
                        depthMeters: depth,
                        intrinsics: intrinsics,
                        cameraTransform: cameraTransform
                    ) else { continue }

                    record(grid.addSample(worldPoint: world, color: sample, maxVoxels: maxVoxels))
                }
            }

            // Carve pass: any existing voxel the camera can now see *through*
            // (observed surface well behind it) accrues a miss and is removed
            // after a few consecutive misses.
            let existingKeys = grid.chunks.values.flatMap { $0.keys }
            for key in existingKeys {
                let center = grid.center(of: key)
                guard let projected = VoxelProjection.pixel(
                    worldPoint: center,
                    intrinsics: intrinsics,
                    cameraTransform: cameraTransform
                ) else { continue }

                let depthX = Int((projected.pixel.x / scaleX).rounded(.down))
                let depthY = Int((projected.pixel.y / scaleY).rounded(.down))
                guard depthX >= 0, depthX < depthWidth, depthY >= 0, depthY < depthHeight else { continue }

                if let confidenceBase {
                    let confidence = confidenceBase[depthY * confidenceBytesPerRow + depthX]
                    guard confidence >= mediumConfidence else { continue }
                }
                let observed = (depthBaseRaw + depthY * depthBytesPerRow)
                    .assumingMemoryBound(to: Float32.self)[depthX]

                switch VoxelCarver.classify(
                    voxelDepth: projected.depthMeters,
                    observedDepth: observed,
                    voxelSize: grid.voxelSize
                ) {
                case .freeSpace:
                    if grid.registerMiss(at: key) {
                        structural.formUnion(grid.affectedChunks(around: key))
                    }
                case .confirmed:
                    grid.registerConfirmation(at: key)
                case .unknown:
                    break
                }
            }
        } else if let featurePoints {
            for point in featurePoints.prefix(maxFeaturePoints) {
                guard let projected = VoxelProjection.pixel(
                    worldPoint: point,
                    intrinsics: intrinsics,
                    cameraTransform: cameraTransform
                ), projected.depthMeters <= maxDepth else { continue }
                guard let sample = sampleColor(
                    imageX: Int(projected.pixel.x),
                    imageY: Int(projected.pixel.y)
                ) else { continue }

                record(grid.addSample(worldPoint: point, color: sample, maxVoxels: maxVoxels))
            }
        }

        return Result(structural: structural, color: color, budgetHit: budgetHit)
    }
}
