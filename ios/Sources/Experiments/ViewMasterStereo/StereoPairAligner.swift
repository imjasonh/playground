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

        let left = swapEyes ? wide : matchedUW
        let right = swapEyes ? matchedUW : wide
        return Pair(
            left: left,
            right: right,
            wide: wide,
            ultraWideMatched: matchedUW,
            appliedZoomFactor: factor
        )
    }

    // MARK: - Sampling

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
