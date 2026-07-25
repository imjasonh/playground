import CoreGraphics
import UIKit

/// Aligns ultra-wide + wide frames into a matched stereo pair for preview.
///
/// Crops the ultra-wide so its field of view matches the wide camera (FOV math,
/// then a small content-based scale refine). Mismatched zoom reads as
/// forward/back motion in a wigglegram instead of left/right parallax.
enum StereoPairAligner {
    /// Fallback when FOV isn't available (~0.5× UW vs wide on many iPhones).
    static let defaultUltraWideZoomFactor: CGFloat = 0.5

    struct Pair {
        let left: UIImage
        let right: UIImage
        let wide: UIImage
        let ultraWideMatched: UIImage
        /// Fraction of the ultra-wide frame retained on each axis before scaling.
        let appliedZoomFactor: CGFloat
    }

    /// Horizontal FOV → center-crop fraction of the UW frame that matches wide.
    /// Uses `tan(fov/2)` so wide angles stay accurate.
    static func cropFactor(wideFOVDegrees: Double, ultraWideFOVDegrees: Double) -> CGFloat {
        guard wideFOVDegrees > 1, ultraWideFOVDegrees > wideFOVDegrees else {
            return defaultUltraWideZoomFactor
        }
        let halfWide = wideFOVDegrees * .pi / 360
        let halfUltra = ultraWideFOVDegrees * .pi / 360
        let factor = tan(halfWide) / tan(halfUltra)
        return CGFloat(min(max(factor, 0.2), 0.95))
    }

    /// Center-crop `image` so the retained fraction of each axis is `zoomFactor`
    /// (e.g. 0.5 keeps the middle half), then scale to `targetSize`.
    static func centerCrop(
        _ image: UIImage,
        zoomFactor: CGFloat,
        targetSize: CGSize
    ) -> UIImage? {
        guard let cgImage = image.cgImage else { return nil }
        let factor = min(max(zoomFactor, 0.05), 1.0)
        let srcW = CGFloat(cgImage.width)
        let srcH = CGFloat(cgImage.height)
        guard srcW > 0, srcH > 0, targetSize.width > 0, targetSize.height > 0 else {
            return nil
        }

        let cropW = srcW * factor
        let cropH = srcH * factor
        let cropRect = CGRect(
            x: (srcW - cropW) * 0.5,
            y: (srcH - cropH) * 0.5,
            width: cropW,
            height: cropH
        ).integral

        guard cropRect.width >= 1, cropRect.height >= 1,
              let cropped = cgImage.cropping(to: cropRect)
        else { return nil }

        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        let renderer = UIGraphicsImageRenderer(size: targetSize, format: format)
        return renderer.image { _ in
            UIImage(cgImage: cropped, scale: 1, orientation: image.imageOrientation)
                .draw(in: CGRect(origin: .zero, size: targetSize))
        }
    }

    /// Refine an FOV-based crop factor by maximizing center-patch similarity.
    /// Searches a narrow band around `estimatedFactor` so residual lens/FOV
    /// error doesn't leave one eye more zoomed than the other.
    static func refinedCropFactor(
        wide: UIImage,
        ultraWide: UIImage,
        estimatedFactor: CGFloat,
        sampleSize: Int = 64,
        searchFraction: CGFloat = 0.12,
        steps: Int = 9
    ) -> CGFloat {
        let base = min(max(estimatedFactor, 0.2), 0.95)
        guard let wideGray = grayscaleSamples(wide, side: sampleSize) else {
            return base
        }

        let lo = max(0.2, base * (1 - searchFraction))
        let hi = min(0.95, base * (1 + searchFraction))
        guard steps > 1, hi > lo else { return base }

        var bestFactor = base
        var bestScore = -Double.greatestFiniteMagnitude

        for i in 0..<steps {
            let t = CGFloat(i) / CGFloat(steps - 1)
            let factor = lo + (hi - lo) * t
            guard
                let cropped = centerCrop(
                    ultraWide,
                    zoomFactor: factor,
                    targetSize: CGSize(width: sampleSize, height: sampleSize)
                ),
                let ultraGray = grayscaleSamples(cropped, side: sampleSize)
            else { continue }

            let score = normalizedCrossCorrelation(wideGray, ultraGray)
            if score > bestScore {
                bestScore = score
                bestFactor = factor
            }
        }
        return bestFactor
    }

    /// Build a stereo pair. Ultra-wide is FOV-matched to wide; eyes may swap
    /// so left/right stay consistent across landscape directions.
    static func makePair(
        wide: UIImage,
        ultraWide: UIImage,
        ultraWideZoomFactor: CGFloat = defaultUltraWideZoomFactor,
        refineScale: Bool = true,
        matchBrightness: Bool = true,
        swapEyes: Bool
    ) -> Pair? {
        let target = wide.size
        guard target.width > 0, target.height > 0 else { return nil }

        let factor: CGFloat
        if refineScale {
            factor = refinedCropFactor(
                wide: wide,
                ultraWide: ultraWide,
                estimatedFactor: ultraWideZoomFactor
            )
        } else {
            factor = min(max(ultraWideZoomFactor, 0.2), 0.95)
        }

        guard let matchedUW = centerCrop(
            ultraWide,
            zoomFactor: factor,
            targetSize: target
        ) else {
            return nil
        }

        let rawLeft = swapEyes ? wide : matchedUW
        let rawRight = swapEyes ? matchedUW : wide
        let matched = matchBrightness
            ? matchLuminance(left: rawLeft, right: rawRight)
            : (left: rawLeft, right: rawRight)
        return Pair(
            left: matched.left,
            right: matched.right,
            wide: wide,
            ultraWideMatched: matchedUW,
            appliedZoomFactor: factor
        )
    }

    /// Match brightness (and mild white balance) so wiggle flicker is reduced.
    ///
    /// Pipeline:
    /// 1. **Midtone** R/G/B gains (ignores clipped near-black / near-white)
    /// 2. Residual **shadow / mid / highlight** luma curve so contrast still matches
    ///    when one eye’s ISP curve differs after a global gain
    ///
    /// Whole-frame mean matching alone fails on backlit scenes where one eye
    /// blows the sky — the average looks fine while plants still flicker.
    static func matchLuminance(left: UIImage, right: UIImage) -> (left: UIImage, right: UIImage) {
        let sampleSide = 96
        guard
            let leftMids = robustChannelMidtones(left, sampleSide: sampleSide),
            let rightMids = robustChannelMidtones(right, sampleSide: sampleSide)
        else {
            return fallbackMeanMatch(left: left, right: right)
        }

        let target = ChannelMidtones(
            r: sharedTarget(leftMids.r, rightMids.r),
            g: sharedTarget(leftMids.g, rightMids.g),
            b: sharedTarget(leftMids.b, rightMids.b)
        )

        let leftScales = ChannelScales(
            r: scale(toward: target.r, from: leftMids.r),
            g: scale(toward: target.g, from: leftMids.g),
            b: scale(toward: target.b, from: leftMids.b)
        )
        let rightScales = ChannelScales(
            r: scale(toward: target.r, from: rightMids.r),
            g: scale(toward: target.g, from: rightMids.g),
            b: scale(toward: target.b, from: rightMids.b)
        )

        let channelLeft = leftScales.isNearlyIdentity
            ? left
            : (applyChannelScales(left, scales: leftScales) ?? left)
        let channelRight = rightScales.isNearlyIdentity
            ? right
            : (applyChannelScales(right, scales: rightScales) ?? right)

        return matchLumaAnchors(left: channelLeft, right: channelRight, sampleSide: sampleSide)
    }

    /// Match shadow / mid / highlight luma percentiles with a piecewise curve.
    static func matchLumaAnchors(
        left: UIImage,
        right: UIImage,
        sampleSide: Int = 96
    ) -> (left: UIImage, right: UIImage) {
        guard
            let leftAnchors = lumaAnchors(left, sampleSide: sampleSide),
            let rightAnchors = lumaAnchors(right, sampleSide: sampleSide)
        else {
            return (left, right)
        }

        let targets = LumaAnchors(
            shadow: sharedTarget(leftAnchors.shadow, rightAnchors.shadow),
            mid: sharedTarget(leftAnchors.mid, rightAnchors.mid),
            highlight: sharedTarget(leftAnchors.highlight, rightAnchors.highlight)
        )

        let adjustedLeft = leftAnchors.isNearlyEqual(to: targets)
            ? left
            : (applyLumaAnchorCurve(left, from: leftAnchors, to: targets) ?? left)
        let adjustedRight = rightAnchors.isNearlyEqual(to: targets)
            ? right
            : (applyLumaAnchorCurve(right, from: rightAnchors, to: targets) ?? right)
        return (adjustedLeft, adjustedRight)
    }

    /// Luma percentiles used as tone-curve anchors (p25 / p50 / p75).
    static func lumaAnchors(
        _ image: UIImage,
        sampleSide: Int = 96,
        clipLow: Float = 0.02,
        clipHigh: Float = 0.98
    ) -> LumaAnchors? {
        guard let samples = grayscaleSamples(image, side: sampleSide), !samples.isEmpty else {
            return nil
        }
        let usable = samples.filter { $0 > clipLow && $0 < clipHigh }
        let pool = usable.count >= max(16, samples.count / 20) ? usable : samples
        guard
            let shadow = percentile(pool, p: 0.25),
            let mid = percentile(pool, p: 0.50),
            let highlight = percentile(pool, p: 0.75)
        else {
            return nil
        }
        return LumaAnchors(
            shadow: Double(shadow),
            mid: Double(mid),
            highlight: Double(highlight)
        )
    }

    /// Whole-frame mean luminance (tests / fallback). Prefer midtones for matching.
    static func meanLuminance(_ image: UIImage, sampleSide: Int = 48) -> Double? {
        guard let samples = grayscaleSamples(image, side: sampleSide), !samples.isEmpty else {
            return nil
        }
        let sum = samples.reduce(0 as Float) { $0 + $1 }
        return Double(sum / Float(samples.count))
    }

    /// Median R/G/B among pixels whose luma sits between the clip rails.
    static func robustChannelMidtones(
        _ image: UIImage,
        sampleSide: Int = 96,
        clipLow: Float = 0.05,
        clipHigh: Float = 0.95
    ) -> ChannelMidtones? {
        guard let pixels = rgbaSamples(image, side: sampleSide), !pixels.isEmpty else {
            return nil
        }

        var rs: [Float] = []
        var gs: [Float] = []
        var bs: [Float] = []
        rs.reserveCapacity(pixels.count / 4)
        gs.reserveCapacity(pixels.count / 4)
        bs.reserveCapacity(pixels.count / 4)

        let count = pixels.count / 4
        for i in 0..<count {
            let o = i * 4
            let r = Float(pixels[o]) / 255
            let g = Float(pixels[o + 1]) / 255
            let b = Float(pixels[o + 2]) / 255
            // Rec. 709-ish luma — good enough for exposure matching.
            let y = 0.2126 * r + 0.7152 * g + 0.0722 * b
            guard y > clipLow, y < clipHigh else { continue }
            rs.append(r)
            gs.append(g)
            bs.append(b)
        }

        // Too much clipping → fall back to all-pixel medians so we still adjust.
        if rs.count < max(16, count / 20) {
            rs.removeAll(keepingCapacity: true)
            gs.removeAll(keepingCapacity: true)
            bs.removeAll(keepingCapacity: true)
            for i in 0..<count {
                let o = i * 4
                rs.append(Float(pixels[o]) / 255)
                gs.append(Float(pixels[o + 1]) / 255)
                bs.append(Float(pixels[o + 2]) / 255)
            }
        }

        guard
            let mr = median(rs),
            let mg = median(gs),
            let mb = median(bs)
        else {
            return nil
        }
        return ChannelMidtones(r: Double(mr), g: Double(mg), b: Double(mb))
    }

    static func applyLuminanceScale(_ image: UIImage, scale: CGFloat) -> UIImage? {
        applyChannelScales(image, scales: ChannelScales(r: scale, g: scale, b: scale))
    }

    static func applyChannelScales(_ image: UIImage, scales: ChannelScales) -> UIImage? {
        guard let cgImage = image.cgImage else { return nil }
        let width = cgImage.width
        let height = cgImage.height
        guard width > 0, height > 0 else { return nil }

        let rScale = min(max(scales.r, 0.35), 2.8)
        let gScale = min(max(scales.g, 0.35), 2.8)
        let bScale = min(max(scales.b, 0.35), 2.8)

        var pixels = [UInt8](repeating: 0, count: width * height * 4)
        let colorSpace = CGColorSpaceCreateDeviceRGB()
        let bitmapInfo = CGImageAlphaInfo.premultipliedLast.rawValue
        guard let context = CGContext(
            data: &pixels,
            width: width,
            height: height,
            bitsPerComponent: 8,
            bytesPerRow: width * 4,
            space: colorSpace,
            bitmapInfo: bitmapInfo
        ) else {
            return nil
        }
        context.draw(cgImage, in: CGRect(x: 0, y: 0, width: width, height: height))

        let count = width * height
        for i in 0..<count {
            let o = i * 4
            pixels[o] = UInt8(min(255, Int((CGFloat(pixels[o]) * rScale).rounded())))
            pixels[o + 1] = UInt8(min(255, Int((CGFloat(pixels[o + 1]) * gScale).rounded())))
            pixels[o + 2] = UInt8(min(255, Int((CGFloat(pixels[o + 2]) * bScale).rounded())))
        }

        guard let out = context.makeImage() else { return nil }
        return UIImage(cgImage: out, scale: image.scale, orientation: image.imageOrientation)
    }

    struct ChannelMidtones: Equatable {
        var r: Double
        var g: Double
        var b: Double
    }

    struct ChannelScales: Equatable {
        var r: CGFloat
        var g: CGFloat
        var b: CGFloat

        var isNearlyIdentity: Bool {
            abs(r - 1) < 0.03 && abs(g - 1) < 0.03 && abs(b - 1) < 0.03
        }
    }

    struct LumaAnchors: Equatable {
        var shadow: Double
        var mid: Double
        var highlight: Double

        func isNearlyEqual(to other: LumaAnchors, tolerance: Double = 0.02) -> Bool {
            abs(shadow - other.shadow) < tolerance
                && abs(mid - other.mid) < tolerance
                && abs(highlight - other.highlight) < tolerance
        }
    }

    // MARK: - Matching helpers

    private static func sharedTarget(_ a: Double, _ b: Double) -> Double {
        max(0.05, sqrt(max(a, 0.01) * max(b, 0.01)))
    }

    private static func scale(toward target: Double, from value: Double) -> CGFloat {
        CGFloat(target / max(value, 0.01))
    }

    private static func fallbackMeanMatch(left: UIImage, right: UIImage) -> (left: UIImage, right: UIImage) {
        let meanL = meanLuminance(left) ?? 0.5
        let meanR = meanLuminance(right) ?? 0.5
        let target = sharedTarget(meanL, meanR)
        let leftScale = scale(toward: target, from: meanL)
        let rightScale = scale(toward: target, from: meanR)
        let adjustedLeft = abs(leftScale - 1) < 0.03
            ? left
            : (applyLuminanceScale(left, scale: leftScale) ?? left)
        let adjustedRight = abs(rightScale - 1) < 0.03
            ? right
            : (applyLuminanceScale(right, scale: rightScale) ?? right)
        return matchLumaAnchors(left: adjustedLeft, right: adjustedRight)
    }

    /// Remap pixel luma toward shared shadow/mid/highlight anchors; preserve chroma.
    static func applyLumaAnchorCurve(
        _ image: UIImage,
        from source: LumaAnchors,
        to target: LumaAnchors
    ) -> UIImage? {
        guard let cgImage = image.cgImage else { return nil }
        let width = cgImage.width
        let height = cgImage.height
        guard width > 0, height > 0 else { return nil }

        let lut = makeLumaLUT(from: source, to: target)
        var pixels = [UInt8](repeating: 0, count: width * height * 4)
        let colorSpace = CGColorSpaceCreateDeviceRGB()
        let bitmapInfo = CGImageAlphaInfo.premultipliedLast.rawValue
        guard let context = CGContext(
            data: &pixels,
            width: width,
            height: height,
            bitsPerComponent: 8,
            bytesPerRow: width * 4,
            space: colorSpace,
            bitmapInfo: bitmapInfo
        ) else {
            return nil
        }
        context.draw(cgImage, in: CGRect(x: 0, y: 0, width: width, height: height))

        let count = width * height
        for i in 0..<count {
            let o = i * 4
            let r = Float(pixels[o]) / 255
            let g = Float(pixels[o + 1]) / 255
            let b = Float(pixels[o + 2]) / 255
            let y = 0.2126 * r + 0.7152 * g + 0.0722 * b
            let idx = min(255, max(0, Int((y * 255).rounded())))
            let yOut = lut[idx]
            let gain = y > 0.001 ? min(max(yOut / y, 0.35), 2.8) : 1
            pixels[o] = UInt8(min(255, Int((r * gain * 255).rounded())))
            pixels[o + 1] = UInt8(min(255, Int((g * gain * 255).rounded())))
            pixels[o + 2] = UInt8(min(255, Int((b * gain * 255).rounded())))
        }

        guard let out = context.makeImage() else { return nil }
        return UIImage(cgImage: out, scale: image.scale, orientation: image.imageOrientation)
    }

    /// Piecewise-linear LUT from source anchors → target anchors (0…1 luma domain).
    static func makeLumaLUT(from source: LumaAnchors, to target: LumaAnchors) -> [Float] {
        let src = [
            0.0,
            min(max(source.shadow, 0.001), 0.999),
            min(max(source.mid, 0.001), 0.999),
            min(max(source.highlight, 0.001), 0.999),
            1.0,
        ]
        // Keep anchor order strictly increasing for stable interpolation.
        var orderedSrc = src
        for i in 1..<orderedSrc.count {
            orderedSrc[i] = max(orderedSrc[i], orderedSrc[i - 1] + 0.001)
        }
        orderedSrc[orderedSrc.count - 1] = 1.0

        let dst = [
            0.0,
            min(max(target.shadow, 0.0), 1.0),
            min(max(target.mid, 0.0), 1.0),
            min(max(target.highlight, 0.0), 1.0),
            1.0,
        ]
        var orderedDst = dst
        for i in 1..<orderedDst.count {
            orderedDst[i] = max(orderedDst[i], orderedDst[i - 1])
        }
        orderedDst[orderedDst.count - 1] = 1.0

        var lut = [Float](repeating: 0, count: 256)
        for i in 0..<256 {
            let x = Double(i) / 255.0
            lut[i] = Float(piecewiseMap(x, source: orderedSrc, destination: orderedDst))
        }
        return lut
    }

    static func piecewiseMap(_ x: Double, source: [Double], destination: [Double]) -> Double {
        guard source.count == destination.count, source.count >= 2 else { return x }
        if x <= source[0] { return destination[0] }
        if x >= source[source.count - 1] { return destination[destination.count - 1] }
        for i in 0..<(source.count - 1) {
            let x0 = source[i]
            let x1 = source[i + 1]
            if x >= x0 && x <= x1 {
                let t = (x - x0) / max(x1 - x0, 1e-6)
                return destination[i] + t * (destination[i + 1] - destination[i])
            }
        }
        return destination[destination.count - 1]
    }

    private static func median(_ values: [Float]) -> Float? {
        percentile(values, p: 0.5)
    }

    private static func percentile(_ values: [Float], p: Double) -> Float? {
        guard !values.isEmpty else { return nil }
        let sorted = values.sorted()
        let clamped = min(max(p, 0), 1)
        let idx = clamped * Double(sorted.count - 1)
        let lo = Int(idx.rounded(.down))
        let hi = min(sorted.count - 1, lo + 1)
        let t = Float(idx - Double(lo))
        return sorted[lo] * (1 - t) + sorted[hi] * t
    }

    // MARK: - Sampling

    private static func rgbaSamples(_ image: UIImage, side: Int) -> [UInt8]? {
        guard side > 0, let cgImage = image.cgImage else { return nil }
        var pixels = [UInt8](repeating: 0, count: side * side * 4)
        let colorSpace = CGColorSpaceCreateDeviceRGB()
        guard let context = CGContext(
            data: &pixels,
            width: side,
            height: side,
            bitsPerComponent: 8,
            bytesPerRow: side * 4,
            space: colorSpace,
            bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
        ) else {
            return nil
        }
        context.interpolationQuality = .medium
        context.draw(cgImage, in: CGRect(x: 0, y: 0, width: side, height: side))
        return pixels
    }

    private static func grayscaleSamples(_ image: UIImage, side: Int) -> [Float]? {
        guard side > 0, let cgImage = image.cgImage else { return nil }
        let bytesPerRow = side
        var pixels = [UInt8](repeating: 0, count: side * side)
        let colorSpace = CGColorSpaceCreateDeviceGray()
        guard let context = CGContext(
            data: &pixels,
            width: side,
            height: side,
            bitsPerComponent: 8,
            bytesPerRow: bytesPerRow,
            space: colorSpace,
            bitmapInfo: CGImageAlphaInfo.none.rawValue
        ) else {
            return nil
        }
        context.interpolationQuality = .medium
        context.draw(cgImage, in: CGRect(x: 0, y: 0, width: side, height: side))
        return pixels.map { Float($0) / 255 }
    }

    private static func normalizedCrossCorrelation(_ a: [Float], _ b: [Float]) -> Double {
        guard a.count == b.count, !a.isEmpty else { return -1 }
        let n = Float(a.count)
        let meanA = a.reduce(0, +) / n
        let meanB = b.reduce(0, +) / n
        var num: Float = 0
        var denA: Float = 0
        var denB: Float = 0
        for i in 0..<a.count {
            let da = a[i] - meanA
            let db = b[i] - meanB
            num += da * db
            denA += da * da
            denB += db * db
        }
        let den = sqrt(Double(denA * denB))
        guard den > 1e-6 else { return -1 }
        return Double(num) / den
    }
}
