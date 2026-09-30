import AVFoundation
import CoreImage
import UIKit

/// Sensor-native camera buffers to an upright image. Same mapping Local Lens uses
/// so the front camera is mirrored and portrait pixels are not rotated twice.
enum HairColorOrientation {
    static func captureOrientation(for deviceOrientation: UIDeviceOrientation) -> AVCaptureVideoOrientation {
        switch deviceOrientation {
        case .portrait:
            return .portrait
        case .portraitUpsideDown:
            return .portraitUpsideDown
        case .landscapeLeft:
            return .landscapeRight
        case .landscapeRight:
            return .landscapeLeft
        default:
            return .portrait
        }
    }

    /// Clockwise degrees for `AVCaptureConnection.videoRotationAngle`.
    /// Portrait is 90, upside down is 270, and the landscape cases swap
    /// the same way `captureOrientation` does.
    static func photoRotationAngle(for deviceOrientation: UIDeviceOrientation) -> CGFloat {
        switch captureOrientation(for: deviceOrientation) {
        case .portrait:
            return 90
        case .portraitUpsideDown:
            return 270
        case .landscapeRight:
            return 0
        case .landscapeLeft:
            return 180
        @unknown default:
            return 90
        }
    }

    static func visionOrientation(
        deviceOrientation: UIDeviceOrientation,
        cameraPosition: AVCaptureDevice.Position
    ) -> CGImagePropertyOrientation {
        let isFront = cameraPosition == .front
        switch deviceOrientation {
        case .portrait:
            return isFront ? .leftMirrored : .right
        case .portraitUpsideDown:
            return isFront ? .rightMirrored : .left
        case .landscapeLeft:
            return isFront ? .downMirrored : .up
        case .landscapeRight:
            return isFront ? .upMirrored : .down
        default:
            return isFront ? .leftMirrored : .right
        }
    }

    static func uprightCIImage(
        from pixelBuffer: CVPixelBuffer,
        orientation: CGImagePropertyOrientation
    ) -> CIImage {
        rebase(CIImage(cvPixelBuffer: pixelBuffer).oriented(orientation))
    }

    static func rebase(_ image: CIImage) -> CIImage {
        let extent = image.extent
        guard extent.origin.x.isFinite, extent.origin.y.isFinite, extent.origin != .zero else {
            return image
        }
        return image.transformed(
            by: CGAffineTransform(translationX: -extent.origin.x, y: -extent.origin.y)
        )
    }

    /// Longest edge becomes `maxEdge`. Smaller images stay as they are.
    static func downscaled(_ image: CIImage, maxEdge: CGFloat) -> CIImage {
        let extent = image.extent
        guard extent.width.isFinite, extent.height.isFinite else { return image }
        let longest = max(extent.width, extent.height)
        guard longest > maxEdge, maxEdge > 0 else { return image }
        let scale = maxEdge / longest
        return image.transformed(by: CGAffineTransform(scaleX: scale, y: scale))
    }
}
