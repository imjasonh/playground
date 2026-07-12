import CoreVideo
import Foundation

/// CPU helpers that turn synchronized color + depth frames into a z-band image.
enum ZDepthBandMasker {
    /// Sample a Float32 depth map (row-major meters) at a normalized UV in `0...1`.
    /// Returns `nil` when the sample is missing or non-finite.
    static func sampleDepthMeters(
        depth: UnsafePointer<Float>,
        depthWidth: Int,
        depthHeight: Int,
        depthBytesPerRow: Int,
        u: Double,
        v: Double
    ) -> Double? {
        guard depthWidth > 0, depthHeight > 0 else { return nil }
        let x = min(depthWidth - 1, max(0, Int((u * Double(depthWidth - 1)).rounded())))
        let y = min(depthHeight - 1, max(0, Int((v * Double(depthHeight - 1)).rounded())))
        let rowFloats = depthBytesPerRow / MemoryLayout<Float>.size
        let value = Double(depth[y * rowFloats + x])
        guard value.isFinite, value > 0 else { return nil }
        return value
    }

    /// Decide whether a video pixel should stay visible for the given band.
    static func shouldKeepPixel(
        depthMeters: Double?,
        band: ZDepthBand
    ) -> Bool {
        guard let depthMeters else { return false }
        return band.contains(depthMeters)
    }

    /// Apply the band in-place to a 32-bit BGRA buffer using a Float32 depth map.
    /// Pixels outside the band (or with invalid depth) become opaque black.
    static func applyBandInPlace(
        bgra: UnsafeMutablePointer<UInt8>,
        width: Int,
        height: Int,
        bytesPerRow: Int,
        depth: UnsafePointer<Float>,
        depthWidth: Int,
        depthHeight: Int,
        depthBytesPerRow: Int,
        band: ZDepthBand,
        mirrorX: Bool
    ) {
        guard width > 0, height > 0 else { return }
        let clamped = band.clamped()

        for y in 0..<height {
            let row = bgra.advanced(by: y * bytesPerRow)
            let v = height == 1 ? 0.0 : Double(y) / Double(height - 1)
            for x in 0..<width {
                let srcX = mirrorX ? (width - 1 - x) : x
                let u = width == 1 ? 0.0 : Double(srcX) / Double(width - 1)
                let depthMeters = sampleDepthMeters(
                    depth: depth,
                    depthWidth: depthWidth,
                    depthHeight: depthHeight,
                    depthBytesPerRow: depthBytesPerRow,
                    u: u,
                    v: v
                )
                if shouldKeepPixel(depthMeters: depthMeters, band: clamped) {
                    continue
                }
                let pixel = row.advanced(by: x * 4)
                pixel[0] = 0 // B
                pixel[1] = 0 // G
                pixel[2] = 0 // R
                pixel[3] = 255 // A
            }
        }
    }

    /// Convenience for unit tests: mask a tightly packed BGRA buffer with a tightly packed depth map.
    static func applyBand(
        bgra: inout [UInt8],
        width: Int,
        height: Int,
        depth: [Float],
        depthWidth: Int,
        depthHeight: Int,
        band: ZDepthBand,
        mirrorX: Bool = false
    ) {
        precondition(bgra.count >= width * height * 4)
        precondition(depth.count >= depthWidth * depthHeight)
        bgra.withUnsafeMutableBufferPointer { bgraBuffer in
            depth.withUnsafeBufferPointer { depthBuffer in
                applyBandInPlace(
                    bgra: bgraBuffer.baseAddress!,
                    width: width,
                    height: height,
                    bytesPerRow: width * 4,
                    depth: depthBuffer.baseAddress!,
                    depthWidth: depthWidth,
                    depthHeight: depthHeight,
                    depthBytesPerRow: depthWidth * MemoryLayout<Float>.size,
                    band: band,
                    mirrorX: mirrorX
                )
            }
        }
    }
}
