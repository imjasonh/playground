import ARKit
import CoreGraphics
import CoreVideo
import simd
import UIKit

/// Turns the part of a camera frame that has no usable depth into chunky
/// palette pixels. Each square is the on-screen size of a voxel sitting at
/// the farthest depth the scanner reports, so the sky and everything past
/// that distance read as the same blocks. Pixels inside the depth range are
/// left alone.
enum FarFieldPixelizer {
    /// Depth samples at or below this are not a surface. Voxel integration
    /// uses the same cutoff.
    static let minimumDepth: Float = 0.05

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

    /// Replaces out-of-range pixels in `pixels` (row-major, RGB 0...1).
    ///
    /// Squares are centered on the principal point and sized with
    /// `focalLength` at `maxDepth`, so a block matches a voxel at the far
    /// shell. `depth` is packed row-major and may be lower resolution than
    /// the image. Pass `nil` when the camera has no depth map. Then the
    /// whole frame is beyond range.
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
        let blockX = blockEdgePixels(focalLength: focalLength.x, voxelEdge: voxelEdge, depth: maxDepth)
        let blockY = blockEdgePixels(focalLength: focalLength.y, voxelEdge: voxelEdge, depth: maxDepth)
        let firstX = blockIndex(pixel: 0, principal: principalPoint.x, block: blockX)
        let lastX = blockIndex(pixel: width - 1, principal: principalPoint.x, block: blockX)
        let firstY = blockIndex(pixel: 0, principal: principalPoint.y, block: blockY)
        let lastY = blockIndex(pixel: height - 1, principal: principalPoint.y, block: blockY)
        let spanX = lastX - firstX + 1
        let spanY = lastY - firstY + 1
        guard spanX > 0, spanY > 0, spanY <= Int.max / spanX else { return }

        var sums = [SIMD3<Float>](repeating: .zero, count: spanX * spanY)
        var counts = [Int](repeating: 0, count: spanX * spanY)

        func slot(x: Int, y: Int) -> Int {
            let bx = blockIndex(pixel: x, principal: principalPoint.x, block: blockX)
            let by = blockIndex(pixel: y, principal: principalPoint.y, block: blockY)
            return (by - firstY) * spanX + (bx - firstX)
        }

        func beyond(x: Int, y: Int) -> Bool {
            let sample = depthSample(
                depth: depth,
                depthWidth: depthWidth,
                depthHeight: depthHeight,
                x: x,
                y: y,
                imageWidth: width,
                imageHeight: height
            )
            return isBeyondRange(depth: sample, maxDepth: maxDepth)
        }

        pixels.withUnsafeMutableBufferPointer { buffer in
            guard let base = buffer.baseAddress else { return }
            for y in 0..<height {
                for x in 0..<width where beyond(x: x, y: y) {
                    let index = slot(x: x, y: y)
                    sums[index] += base[y * width + x]
                    counts[index] += 1
                }
            }

            var colors = [SIMD3<Float>](repeating: .zero, count: sums.count)
            for index in sums.indices where counts[index] > 0 {
                colors[index] = VoxelPalette.quantize(sums[index] / Float(counts[index]))
            }

            for y in 0..<height {
                for x in 0..<width where beyond(x: x, y: y) {
                    base[y * width + x] = colors[slot(x: x, y: y)]
                }
            }
        }
    }

    private static func blockIndex(pixel: Int, principal: Float, block: Int) -> Int {
        let relative = Float(pixel) + 0.5 - principal
        return Int(floor(relative / Float(block)))
    }
}

/// Camera-image texture for the far shell. In-range pixels are transparent
/// so the live camera shows through. Out-of-range pixels are opaque blocks.
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

        if rgb.count != imageWidth * imageHeight {
            rgb = [SIMD3<Float>](repeating: .zero, count: imageWidth * imageHeight)
        }
        for y in 0..<imageHeight {
            for x in 0..<imageWidth {
                let lumaSample = luma[y * lumaBytesPerRow + x]
                let cx = min(x / 2, chromaWidth - 1)
                let cy = min(y / 2, chromaHeight - 1)
                let cb = chroma[cy * chromaBytesPerRow + cx * 2]
                let cr = chroma[cy * chromaBytesPerRow + cx * 2 + 1]
                rgb[y * imageWidth + x] = VoxelColorConversion.rgb(y: lumaSample, cb: cb, cr: cr)
            }
        }

        let depth = Self.packedDepth(frame.smoothedSceneDepth?.depthMap ?? frame.sceneDepth?.depthMap)
        let intrinsics = frame.camera.intrinsics
        FarFieldPixelizer.apply(
            pixels: &rgb,
            width: imageWidth,
            height: imageHeight,
            depth: depth?.values,
            depthWidth: depth?.width ?? 0,
            depthHeight: depth?.height ?? 0,
            principalPoint: SIMD2(intrinsics[2][0], intrinsics[2][1]),
            focalLength: SIMD2(intrinsics[0][0], intrinsics[1][1]),
            maxDepth: VoxelWorldSession.maxDepthMeters,
            voxelEdge: VoxelWorldSession.voxelEdgeMeters
        )

        guard let image = Self.maskedImage(
            pixels: rgb,
            width: imageWidth,
            height: imageHeight,
            depth: depth?.values,
            depthWidth: depth?.width ?? 0,
            depthHeight: depth?.height ?? 0
        ) else {
            return nil
        }
        return FarFieldTexture(
            image: image,
            intrinsics: intrinsics,
            imageWidth: imageWidth,
            imageHeight: imageHeight
        )
    }

    private static func maskedImage(
        pixels: [SIMD3<Float>],
        width: Int,
        height: Int,
        depth: [Float]?,
        depthWidth: Int,
        depthHeight: Int
    ) -> UIImage? {
        guard pixels.count == width * height else { return nil }
        var rgba = [UInt8](repeating: 0, count: width * height * 4)
        for y in 0..<height {
            for x in 0..<width {
                let sample = FarFieldPixelizer.depthSample(
                    depth: depth,
                    depthWidth: depthWidth,
                    depthHeight: depthHeight,
                    x: x,
                    y: y,
                    imageWidth: width,
                    imageHeight: height
                )
                let offset = (y * width + x) * 4
                guard FarFieldPixelizer.isBeyondRange(depth: sample, maxDepth: VoxelWorldSession.maxDepthMeters) else {
                    continue
                }
                let pixel = pixels[y * width + x]
                rgba[offset] = byte(pixel.x)
                rgba[offset + 1] = byte(pixel.y)
                rgba[offset + 2] = byte(pixel.z)
                rgba[offset + 3] = 255
            }
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
