import AVFoundation
import CoreGraphics
import UIKit

/// Maps Vision-normalized geometry (origin bottom-left, upright image space) into
/// a view that aspect-fills that image — including letterbox/pillarbox crop.
enum LocalLensCoordinateMapper {
    /// Aspect-fill transform from image pixels into the view.
    struct ContentTransform: Equatable {
        let scale: CGFloat
        let offsetX: CGFloat
        let offsetY: CGFloat
        let imageSize: CGSize
        let viewSize: CGSize

        static func aspectFill(imageSize: CGSize, viewSize: CGSize) -> ContentTransform {
            let safeImage = CGSize(
                width: max(imageSize.width, 1),
                height: max(imageSize.height, 1)
            )
            let safeView = CGSize(
                width: max(viewSize.width, 1),
                height: max(viewSize.height, 1)
            )
            let scale = max(safeView.width / safeImage.width, safeView.height / safeImage.height)
            let scaledW = safeImage.width * scale
            let scaledH = safeImage.height * scale
            return ContentTransform(
                scale: scale,
                offsetX: (safeView.width - scaledW) / 2,
                offsetY: (safeView.height - scaledH) / 2,
                imageSize: safeImage,
                viewSize: safeView
            )
        }

        func viewPoint(imagePoint: CGPoint) -> CGPoint {
            CGPoint(
                x: imagePoint.x * scale + offsetX,
                y: imagePoint.y * scale + offsetY
            )
        }

        func viewRect(imageRect: CGRect) -> CGRect {
            CGRect(
                x: imageRect.origin.x * scale + offsetX,
                y: imageRect.origin.y * scale + offsetY,
                width: imageRect.width * scale,
                height: imageRect.height * scale
            )
        }
    }

    /// Vision-normalized point (origin bottom-left) → image-pixel point (origin top-left).
    static func imagePoint(
        fromVisionNormalized point: CGPoint,
        imageSize: CGSize
    ) -> CGPoint {
        CGPoint(
            x: point.x * imageSize.width,
            y: (1 - point.y) * imageSize.height
        )
    }

    /// Vision-normalized rect (origin bottom-left) → image-pixel rect (origin top-left).
    static func imageRect(
        fromVisionNormalized box: CGRect,
        imageSize: CGSize
    ) -> CGRect {
        CGRect(
            x: box.origin.x * imageSize.width,
            y: (1 - box.origin.y - box.height) * imageSize.height,
            width: box.width * imageSize.width,
            height: box.height * imageSize.height
        )
    }

    static func viewPoint(
        fromVisionNormalized point: CGPoint,
        imageSize: CGSize,
        viewSize: CGSize
    ) -> CGPoint {
        let transform = ContentTransform.aspectFill(imageSize: imageSize, viewSize: viewSize)
        return transform.viewPoint(imagePoint: imagePoint(fromVisionNormalized: point, imageSize: transform.imageSize))
    }

    static func viewRect(
        fromVisionNormalized box: CGRect,
        imageSize: CGSize,
        viewSize: CGSize
    ) -> CGRect {
        let transform = ContentTransform.aspectFill(imageSize: imageSize, viewSize: viewSize)
        return transform.viewRect(imageRect: imageRect(fromVisionNormalized: box, imageSize: transform.imageSize))
    }

    /// UIDevice → AVCaptureVideoOrientation. Landscape axes are swapped by design.
    static func captureOrientation(for deviceOrientation: UIDeviceOrientation) -> AVCaptureVideoOrientation {
        switch deviceOrientation {
        case .portrait:
            return .portrait
        case .portraitUpsideDown:
            return .portraitUpsideDown
        case .landscapeLeft:
            // Device rotated left (home/island on the right).
            return .landscapeRight
        case .landscapeRight:
            return .landscapeLeft
        default:
            return .portrait
        }
    }
}
