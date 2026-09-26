import ARKit
import CoreGraphics
import CoreVideo
import simd
import UIKit

/// Replaces the camera image with chunky palette pixels so the photo never
/// shows through. Each square is the on-screen size of a voxel at that
/// pixel's depth. Samples with no depth use the scanner maximum.
enum FarFieldPixelizer {
    /// Longest edge of the live shell texture, in pixels.
    ///
    /// A full ARKit camera frame is much finer than a 10 cm block. Compositing
    /// that frame at native size makes the shell trail the phone. This cap
    /// keeps the on-screen block size and drops the extra pixels.
    static let maxTextureEdge = 480

    /// Depth samples at or below this are not a surface. Voxel integration
    /// uses the same cutoff.
    static let minimumDepth: Float = 0.05

    /// Integer factor that brings the longer image edge down to `maxEdge`.
    /// Returns 1 when the image is already within the cap.
    static func sampleScale(width: Int, height: Int, maxEdge: Int = maxTextureEdge) -> Int {
        guard width > 0, height > 0, maxEdge > 0 else { return 1 }
        let longEdge = max(width, height)
        guard longEdge > maxEdge else { return 1 }
        return (longEdge + maxEdge - 1) / maxEdge
    }

    /// Width, height, and scale of the shell texture for a camera image.
    static func sampledSize(
        width: Int,
        height: Int,
        maxEdge: Int = maxTextureEdge
    ) -> (width: Int, height: Int, scale: Int) {
        let scale = sampleScale(width: width, height: height, maxEdge: maxEdge)
        return (max(1, width / scale), max(1, height / scale), scale)
    }

    /// Intrinsics for an image downsampled by `scale` on both axes.
    /// Dividing focal length and principal point by the same factor keeps
    /// the shell plane the same size in the camera.
    static func scaledIntrinsics(_ intrinsics: simd_float3x3, scale: Int) -> simd_float3x3 {
        guard scale > 1 else { return intrinsics }
        let factor = Float(scale)
        var scaled = intrinsics
        var xColumn = scaled[0]
        xColumn.x /= factor
        scaled[0] = xColumn
        var yColumn = scaled[1]
        yColumn.y /= factor
        scaled[1] = yColumn
        var principal = scaled[2]
        principal.x /= factor
        principal.y /= factor
        scaled[2] = principal
        return scaled
    }

    /// Image-pixel edge of one voxel `voxelEdge` meters away at `depth`.
    static func blockEdgePixels(focalLength: Float, voxelEdge: Float, depth: Float) -> Int {
        guard focalLength > 0, voxelEdge > 0, depth > 0, focalLength.isFinite, depth.isFinite else {
            return 1
        }
        let pixels = focalLength * voxelEdge / depth
        guard pixels.isFinite else { return 1 }
        return max(1, Int(pixels.rounded()))
    }

    /// Missing, non-finite, and farther-than-`maxDepth` samples are pixelized.
    static func isBeyondRange(depth: Float, maxDepth: Float, minimumDepth: Float = minimumDepth) -> Bool {
        !(depth.isFinite && depth > minimumDepth && depth <= maxDepth)
    }

    /// Depth used to size a chunk. Missing samples use `maxDepth`. Other
    /// samples snap down to a multiple of `voxelEdge` so neighbors share a grid.
    static func chunkDepth(sample: Float, maxDepth: Float, voxelEdge: Float) -> Float {
        let edge = voxelEdge > 0 ? voxelEdge : minimumDepth
        let capped = isBeyondRange(depth: sample, maxDepth: maxDepth) ? maxDepth : min(sample, maxDepth)
        let steps = floor((capped / edge) + 0.001)
        return min(max(1, steps) * edge, maxDepth)
    }

    /// Nearest depth sample for an image pixel. No depth map, or a short
    /// buffer, is treated as missing (NaN), which is beyond range.
    static func depthSample(
        depth: [Float]?,
        depthWidth: Int,
        depthHeight: Int,
        x: Int,
        y: Int,
        imageWidth: Int,
        imageHeight: Int
    ) -> Float {
        guard
            let depth,
            depthWidth > 0, depthHeight > 0, imageWidth > 0, imageHeight > 0,
            depth.count >= depthWidth * depthHeight
        else {
            return .nan
        }
        let dx = min(depthWidth - 1, x * depthWidth / imageWidth)
        let dy = min(depthHeight - 1, y * depthHeight / imageHeight)
        return depth[dy * depthWidth + dx]
    }

    private struct ChunkKey: Hashable {
        var shellMillis: Int32
        var x: Int32
        var y: Int32
    }

    /// Replaces every pixel in `pixels` (row-major, RGB 0...1) with a palette
    /// color. Squares are centered on the principal point. `depth` is packed
    /// row-major and may be lower resolution than the image. Pass `nil` when
    /// the camera has no depth map. Then every square is sized at `maxDepth`.
    static func apply(
        pixels: inout [SIMD3<Float>],
        width: Int,
        height: Int,
        depth: [Float]?,
        depthWidth: Int,
        depthHeight: Int,
        principalPoint: SIMD2<Float>,
        focalLength: SIMD2<Float>,
        maxDepth: Float,
        voxelEdge: Float
    ) {
        guard width > 0, height > 0, pixels.count == width * height else { return }

        pixels.withUnsafeMutableBufferPointer { buffer in
            guard let base = buffer.baseAddress else { return }
            var sums: [ChunkKey: SIMD3<Float>] = [:]
            var counts: [ChunkKey: Int] = [:]
            var blockCache: [Int32: (Int, Int)] = [:]
            sums.reserveCapacity(4096)
            counts.reserveCapacity(4096)

            func key(x: Int, y: Int) -> ChunkKey {
                let sample = depthSample(
                    depth: depth,
                    depthWidth: depthWidth,
                    depthHeight: depthHeight,
                    x: x,
                    y: y,
                    imageWidth: width,
                    imageHeight: height
                )
                let shell = chunkDepth(sample: sample, maxDepth: maxDepth, voxelEdge: voxelEdge)
                let millis = Int32((shell * 1000).rounded())
                let blocks: (Int, Int)
                if let cached = blockCache[millis] {
                    blocks = cached
                } else {
                    blocks = (
                        blockEdgePixels(focalLength: focalLength.x, voxelEdge: voxelEdge, depth: shell),
                        blockEdgePixels(focalLength: focalLength.y, voxelEdge: voxelEdge, depth: shell)
                    )
                    blockCache[millis] = blocks
                }
                return ChunkKey(
                    shellMillis: millis,
                    x: Int32(blockIndex(pixel: x, principal: principalPoint.x, block: blocks.0)),
                    y: Int32(blockIndex(pixel: y, principal: principalPoint.y, block: blocks.1))
                )
            }

            for y in 0..<height {
                for x in 0..<width {
                    let chunk = key(x: x, y: y)
                    var sum = sums[chunk] ?? .zero
                    sum += base[y * width + x]
                    sums[chunk] = sum
                    counts[chunk, default: 0] += 1
                }
            }

            var colors: [ChunkKey: SIMD3<Float>] = [:]
            colors.reserveCapacity(sums.count)
            for (chunk, sum) in sums {
                let count = Float(counts[chunk] ?? 1)
                colors[chunk] = VoxelPalette.quantize(sum / count)
            }

            for y in 0..<height {
                for x in 0..<width {
                    let chunk = key(x: x, y: y)
                    if let color = colors[chunk] {
                        base[y * width + x] = color
                    }
                }
            }
        }
    }

    private static func blockIndex(pixel: Int, principal: Float, block: Int) -> Int {
        let relative = Float(pixel) + 0.5 - principal
        return Int(floor(relative / Float(block)))
    }
}

/// Opaque camera-image texture. Every texel is a palette block, so the live
/// photo cannot show through gaps in the voxel mesh.
struct FarFieldTexture {
    var image: UIImage
    var intrinsics: simd_float3x3
    var imageWidth: Int
    var imageHeight: Int
}

/// Builds that texture from an ARKit frame.
final class FarFieldCompositor {
    private var rgb: [SIMD3<Float>] = []

    func texture(frame: ARFrame) -> FarFieldTexture? {
        let pixelBuffer = frame.capturedImage
        CVPixelBufferLockBaseAddress(pixelBuffer, .readOnly)
        defer { CVPixelBufferUnlockBaseAddress(pixelBuffer, .readOnly) }
        guard
            CVPixelBufferGetPlaneCount(pixelBuffer) >= 2,
            let lumaBase = CVPixelBufferGetBaseAddressOfPlane(pixelBuffer, 0),
            let chromaBase = CVPixelBufferGetBaseAddressOfPlane(pixelBuffer, 1)
        else {
            return nil
        }

        let imageWidth = CVPixelBufferGetWidthOfPlane(pixelBuffer, 0)
        let imageHeight = CVPixelBufferGetHeightOfPlane(pixelBuffer, 0)
        guard imageWidth > 0, imageHeight > 0 else { return nil }

        let luma = lumaBase.assumingMemoryBound(to: UInt8.self)
        let chroma = chromaBase.assumingMemoryBound(to: UInt8.self)
        let lumaBytesPerRow = CVPixelBufferGetBytesPerRowOfPlane(pixelBuffer, 0)
        let chromaBytesPerRow = CVPixelBufferGetBytesPerRowOfPlane(pixelBuffer, 1)
        let chromaWidth = CVPixelBufferGetWidthOfPlane(pixelBuffer, 1)
        let chromaHeight = CVPixelBufferGetHeightOfPlane(pixelBuffer, 1)

        let sampled = FarFieldPixelizer.sampledSize(width: imageWidth, height: imageHeight)
        let scale = sampled.scale
        let outWidth = sampled.width
        let outHeight = sampled.height
        // Center of each source bin. The shell is chunky enough that the
        // half-bin shift against scaled intrinsics does not show.
        let sampleOffset = scale / 2

        if rgb.count != outWidth * outHeight {
            rgb = [SIMD3<Float>](repeating: .zero, count: outWidth * outHeight)
        }
        for y in 0..<outHeight {
            let sourceY = min(y * scale + sampleOffset, imageHeight - 1)
            let lumaRow = sourceY * lumaBytesPerRow
            for x in 0..<outWidth {
                let sourceX = min(x * scale + sampleOffset, imageWidth - 1)
                let lumaSample = luma[lumaRow + sourceX]
                let cx = min(sourceX / 2, chromaWidth - 1)
                let cy = min(sourceY / 2, chromaHeight - 1)
                let cb = chroma[cy * chromaBytesPerRow + cx * 2]
                let cr = chroma[cy * chromaBytesPerRow + cx * 2 + 1]
                rgb[y * outWidth + x] = VoxelColorConversion.rgb(y: lumaSample, cb: cb, cr: cr)
            }
        }

        let depth = Self.packedDepth(frame.smoothedSceneDepth?.depthMap ?? frame.sceneDepth?.depthMap)
        let intrinsics = FarFieldPixelizer.scaledIntrinsics(frame.camera.intrinsics, scale: scale)
        FarFieldPixelizer.apply(
            pixels: &rgb,
            width: outWidth,
            height: outHeight,
            depth: depth?.values,
            depthWidth: depth?.width ?? 0,
            depthHeight: depth?.height ?? 0,
            principalPoint: SIMD2(intrinsics[2][0], intrinsics[2][1]),
            focalLength: SIMD2(intrinsics[0][0], intrinsics[1][1]),
            maxDepth: VoxelWorldSession.maxDepthMeters,
            voxelEdge: VoxelWorldSession.voxelEdgeMeters
        )

        guard let image = Self.opaqueImage(pixels: rgb, width: outWidth, height: outHeight) else {
            return nil
        }
        return FarFieldTexture(
            image: image,
            intrinsics: intrinsics,
            imageWidth: outWidth,
            imageHeight: outHeight
        )
    }

    private static func opaqueImage(pixels: [SIMD3<Float>], width: Int, height: Int) -> UIImage? {
        guard pixels.count == width * height else { return nil }
        var rgba = [UInt8](repeating: 255, count: width * height * 4)
        for index in pixels.indices {
            let pixel = pixels[index]
            let offset = index * 4
            rgba[offset] = byte(pixel.x)
            rgba[offset + 1] = byte(pixel.y)
            rgba[offset + 2] = byte(pixel.z)
        }
        let info = CGBitmapInfo.byteOrder32Big.rawValue | CGImageAlphaInfo.premultipliedLast.rawValue
        let image: CGImage? = rgba.withUnsafeMutableBytes { raw in
            guard let context = CGContext(
                data: raw.baseAddress,
                width: width,
                height: height,
                bitsPerComponent: 8,
                bytesPerRow: width * 4,
                space: CGColorSpaceCreateDeviceRGB(),
                bitmapInfo: info
            ) else {
                return nil
            }
            return context.makeImage()
        }
        guard let image else { return nil }
        return UIImage(cgImage: image)
    }

    private static func packedDepth(_ buffer: CVPixelBuffer?) -> (values: [Float], width: Int, height: Int)? {
        guard let buffer else { return nil }
        CVPixelBufferLockBaseAddress(buffer, .readOnly)
        defer { CVPixelBufferUnlockBaseAddress(buffer, .readOnly) }
        let width = CVPixelBufferGetWidth(buffer)
        let height = CVPixelBufferGetHeight(buffer)
        let bytesPerRow = CVPixelBufferGetBytesPerRow(buffer)
        guard width > 0, height > 0, let base = CVPixelBufferGetBaseAddress(buffer) else { return nil }
        var values = [Float](repeating: 0, count: width * height)
        for y in 0..<height {
            let row = base.advanced(by: y * bytesPerRow).assumingMemoryBound(to: Float.self)
            for x in 0..<width {
                values[y * width + x] = row[x]
            }
        }
        return (values, width, height)
    }

    private static func byte(_ channel: Float) -> UInt8 {
        let scaled = channel * 255
        guard scaled.isFinite else { return 0 }
        return UInt8(min(255, max(0, Int(scaled.rounded()))))
    }
}
