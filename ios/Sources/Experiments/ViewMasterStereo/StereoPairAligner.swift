import CoreGraphics
import UIKit

/// Aligns ultra-wide + wide frames into a matched stereo pair for preview.
///
/// Matches Apple's spatial-video idea: crop/scale the wider ultra-wide frame so
/// its field of view roughly matches the wide camera, then output equal-size
/// left/right images suitable for a wigglegram or a View-Master service.
enum StereoPairAligner {
    /// Default UW zoom factor relative to wide (~0.5× lens → crop center 50%).
    static let defaultUltraWideZoomFactor: CGFloat = 0.5

    struct Pair {
        let left: UIImage
        let right: UIImage
        let wide: UIImage
        let ultraWideMatched: UIImage
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

        guard let cropped = cgImage.cropping(to: cropRect) else { return nil }

        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        let renderer = UIGraphicsImageRenderer(size: targetSize, format: format)
        return renderer.image { _ in
            UIImage(cgImage: cropped, scale: 1, orientation: image.imageOrientation)
                .draw(in: CGRect(origin: .zero, size: targetSize))
        }
    }

    /// Build a stereo pair. Ultra-wide is FOV-matched to wide; eyes may swap
    /// so left/right stay consistent across landscape directions.
    static func makePair(
        wide: UIImage,
        ultraWide: UIImage,
        ultraWideZoomFactor: CGFloat = defaultUltraWideZoomFactor,
        swapEyes: Bool
    ) -> Pair? {
        let target = wide.size
        guard target.width > 0, target.height > 0 else { return nil }
        guard let matchedUW = centerCrop(
            ultraWide,
            zoomFactor: ultraWideZoomFactor,
            targetSize: target
        ) else {
            return nil
        }

        let left = swapEyes ? wide : matchedUW
        let right = swapEyes ? matchedUW : wide
        return Pair(left: left, right: right, wide: wide, ultraWideMatched: matchedUW)
    }
}
