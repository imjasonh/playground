import CoreVideo
import Foundation

/// CPU helpers that turn synchronized color + depth frames into a z-band image.
enum ZDepthBandMasker {
    /// Blend strength of the blue overlay (0…1).
    static let overlayAlpha: Double = 0.48

    private static func depthValue(
        depth: UnsafePointer<Float>,
        depthWidth: Int,
        depthHeight: Int,
        depthBytesPerRow: Int,
        x: Int,
        y: Int
    ) -> Double? {
        guard x >= 0, y >= 0, x < depthWidth, y < depthHeight else { return nil }
        let rowFloats = depthBytesPerRow / MemoryLayout<Float>.size
        let value = Double(depth[y * rowFloats + x])
        guard value.isFinite, value > 0 else { return nil }
        return value
    }

    /// Sample a Float32 depth map with bilinear interpolation at normalized UV in `0...1`.
    /// Returns `nil` when the neighborhood is missing or non-finite.
    static func sampleDepthMeters(
        depth: UnsafePointer<Float>,
        depthWidth: Int,
        depthHeight: Int,
        depthBytesPerRow: Int,
        u: Double,
        v: Double
    ) -> Double? {
        guard depthWidth > 0, depthHeight > 0 else { return nil }

        if depthWidth == 1 && depthHeight == 1 {
            return depthValue(depth: depth, depthWidth: depthWidth, depthHeight: depthHeight, depthBytesPerRow: depthBytesPerRow, x: 0, y: 0)
        }

        let fx = u * Double(depthWidth - 1)
        let fy = v * Double(depthHeight - 1)
        let x0 = Int(floor(fx))
        let y0 = Int(floor(fy))
        let x1 = min(depthWidth - 1, x0 + 1)
        let y1 = min(depthHeight - 1, y0 + 1)
        let tx = fx - Double(x0)
        let ty = fy - Double(y0)

        guard
            let d00 = depthValue(depth: depth, depthWidth: depthWidth, depthHeight: depthHeight, depthBytesPerRow: depthBytesPerRow, x: x0, y: y0),
            let d10 = depthValue(depth: depth, depthWidth: depthWidth, depthHeight: depthHeight, depthBytesPerRow: depthBytesPerRow, x: x1, y: y0),
            let d01 = depthValue(depth: depth, depthWidth: depthWidth, depthHeight: depthHeight, depthBytesPerRow: depthBytesPerRow, x: x0, y: y1),
            let d11 = depthValue(depth: depth, depthWidth: depthWidth, depthHeight: depthHeight, depthBytesPerRow: depthBytesPerRow, x: x1, y: y1)
        else {
            return nil
        }

        let top = d00 * (1 - tx) + d10 * tx
        let bottom = d01 * (1 - tx) + d11 * tx
        return top * (1 - ty) + bottom * ty
    }

    /// Decide whether a video pixel should stay visible for the given band.
    static func shouldKeepPixel(
        depthMeters: Double?,
        band: ZDepthBand
    ) -> Bool {
        guard let depthMeters else { return false }
        return band.contains(depthMeters)
    }

    /// Finite meter span used to colorize depths when the selection band is open-ended.
    static func overlayRange(for band: ZDepthBand) -> (near: Double, far: Double) {
        let clamped = band.clamped()
        let near = clamped.near.finiteMeters ?? 0
        let far: Double
        switch clamped.far {
        case .infinity:
            far = max(near + 0.5, ZDepthSliderMapping.finiteCapMeters)
        case .meters(let meters):
            far = max(near + 0.01, meters)
        }
        return (near, far)
    }

    /// Map depth to a 0…1 tone inside the overlay range (0 = nearest / lightest).
    static func overlayTone(depthMeters: Double, near: Double, far: Double) -> Double {
        let span = max(0.01, far - near)
        return min(1, max(0, (depthMeters - near) / span))
    }

    /// Light blue (near) → darker blue (far), returned as BGRA components 0…255.
    static func overlayBlueBGRA(tone: Double) -> (b: UInt8, g: UInt8, r: UInt8) {
        let t = min(1, max(0, tone))
        // Near: light sky blue. Far: deep navy.
        let nearB = 245.0, nearG = 210.0, nearR = 150.0
        let farB = 140.0, farG = 55.0, farR = 20.0
        let b = nearB + (farB - nearB) * t
        let g = nearG + (farG - nearG) * t
        let r = nearR + (farR - nearR) * t
        return (UInt8(b.rounded()), UInt8(g.rounded()), UInt8(r.rounded()))
    }

    /// Blend `overlay` over `src` with constant alpha. Channels are BGRA bytes.
    static func blendOverlay(
        srcB: UInt8, srcG: UInt8, srcR: UInt8,
        overlayB: UInt8, overlayG: UInt8, overlayR: UInt8,
        alpha: Double
    ) -> (b: UInt8, g: UInt8, r: UInt8) {
        let a = min(1, max(0, alpha))
        let inv = 1 - a
        let b = Double(srcB) * inv + Double(overlayB) * a
        let g = Double(srcG) * inv + Double(overlayG) * a
        let r = Double(srcR) * inv + Double(overlayR) * a
        return (UInt8(b.rounded()), UInt8(g.rounded()), UInt8(r.rounded()))
    }

    /// Apply the band in-place to a 32-bit BGRA buffer using a Float32 depth map.
    /// Pixels outside the band (or with invalid depth) become opaque black.
    /// When `overlayDepth` is true, kept pixels get a translucent blue tint by depth band.
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
        mapper: ZDepthCoordinateMapper,
        mirrorX: Bool,
        overlayDepth: Bool = false
    ) {
        guard width > 0, height > 0 else { return }
        let clamped = band.clamped()
        let range = overlayRange(for: clamped)

        for y in 0..<height {
            let row = bgra.advanced(by: y * bytesPerRow)
            for x in 0..<width {
                let (u, v) = mapper.depthUV(videoX: x, videoY: y, mirrorX: mirrorX)
                let depthMeters = sampleDepthMeters(
                    depth: depth,
                    depthWidth: depthWidth,
                    depthHeight: depthHeight,
                    depthBytesPerRow: depthBytesPerRow,
                    u: u,
                    v: v
                )
                let pixel = row.advanced(by: x * 4)
                guard shouldKeepPixel(depthMeters: depthMeters, band: clamped) else {
                    pixel[0] = 0 // B
                    pixel[1] = 0 // G
                    pixel[2] = 0 // R
                    pixel[3] = 255 // A
                    continue
                }
                guard overlayDepth, let depthMeters else { continue }

                let tone = overlayTone(depthMeters: depthMeters, near: range.near, far: range.far)
                let blue = overlayBlueBGRA(tone: tone)
                let blended = blendOverlay(
                    srcB: pixel[0], srcG: pixel[1], srcR: pixel[2],
                    overlayB: blue.b, overlayG: blue.g, overlayR: blue.r,
                    alpha: overlayAlpha
                )
                pixel[0] = blended.b
                pixel[1] = blended.g
                pixel[2] = blended.r
                pixel[3] = 255
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
        mirrorX: Bool = false,
        overlayDepth: Bool = false
    ) {
        precondition(bgra.count >= width * height * 4)
        precondition(depth.count >= depthWidth * depthHeight)
        let mapper = ZDepthCoordinateMapper(
            videoWidth: width,
            videoHeight: height,
            depthWidth: depthWidth,
            depthHeight: depthHeight
        )
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
                    mapper: mapper,
                    mirrorX: mirrorX,
                    overlayDepth: overlayDepth
                )
            }
        }
    }
}
