import Foundation
import simd

/// Pinhole camera math shared by depth-map unprojection (LiDAR path) and
/// feature-point projection (non-LiDAR fallback).
///
/// Conventions match ARKit: `intrinsics` is column-major with
/// `fx = m[0][0]`, `fy = m[1][1]`, `cx = m[2][0]`, `cy = m[2][1]`; image `y`
/// grows downward; camera space has `+y` up and the camera looking down `−z`;
/// `cameraTransform` maps camera space to world space.
enum VoxelProjection {
    /// World position of an image pixel observed at a metric depth.
    static func worldPoint(
        pixel: SIMD2<Float>,
        depthMeters: Float,
        intrinsics: simd_float3x3,
        cameraTransform: simd_float4x4
    ) -> SIMD3<Float>? {
        guard depthMeters.isFinite, depthMeters > 0 else { return nil }
        let fx = intrinsics[0][0]
        let fy = intrinsics[1][1]
        let cx = intrinsics[2][0]
        let cy = intrinsics[2][1]
        guard fx != 0, fy != 0 else { return nil }

        let local = SIMD4<Float>(
            (pixel.x - cx) * depthMeters / fx,
            -(pixel.y - cy) * depthMeters / fy,
            -depthMeters,
            1
        )
        let world = cameraTransform * local
        return SIMD3<Float>(world.x, world.y, world.z)
    }

    /// Image pixel a world point lands on, or `nil` when it is behind the
    /// camera. `depthMeters` is the point's distance along the view axis.
    static func pixel(
        worldPoint: SIMD3<Float>,
        intrinsics: simd_float3x3,
        cameraTransform: simd_float4x4
    ) -> (pixel: SIMD2<Float>, depthMeters: Float)? {
        let local = cameraTransform.inverse * SIMD4<Float>(worldPoint, 1)
        let depth = -local.z
        guard depth > 0.001 else { return nil }

        let fx = intrinsics[0][0]
        let fy = intrinsics[1][1]
        let cx = intrinsics[2][0]
        let cy = intrinsics[2][1]

        let u = fx * (local.x / depth) + cx
        let v = fy * (-local.y / depth) + cy
        return (SIMD2<Float>(u, v), depth)
    }
}

/// Full-range BT.601 YCbCr → RGB, the encoding of ARKit's captured image
/// (`420YpCbCr8BiPlanarFullRange`).
enum VoxelColorConversion {
    /// Returns RGB components in `0...1`.
    static func rgb(y: UInt8, cb: UInt8, cr: UInt8) -> SIMD3<Float> {
        let luma = Float(y)
        let blueDiff = Float(cb) - 128
        let redDiff = Float(cr) - 128

        let rgb = SIMD3<Float>(
            luma + 1.402 * redDiff,
            luma - 0.344136 * blueDiff - 0.714136 * redDiff,
            luma + 1.772 * blueDiff
        )
        return simd_clamp(rgb / 255, SIMD3<Float>(repeating: 0), SIMD3<Float>(repeating: 1))
    }
}
