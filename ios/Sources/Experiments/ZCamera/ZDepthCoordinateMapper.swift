import AVFoundation
import CoreMedia

/// Maps video-frame pixel coordinates onto normalized depth-map UVs.
///
/// Synchronized `AVDepthData` is warped to match its paired color buffer, but the
/// depth raster is often lower resolution. When calibration is available we scale
/// through the intrinsics reference dimensions; otherwise we fall back to a simple
/// aspect-preserving stretch.
struct ZDepthCoordinateMapper: Equatable, Sendable {
    let videoWidth: Int
    let videoHeight: Int
    let depthWidth: Int
    let depthHeight: Int
    /// Multiply a video pixel coordinate by this to reach depth-map pixel space.
    let depthScaleX: Double
    let depthScaleY: Double

    init(
        videoWidth: Int,
        videoHeight: Int,
        depthWidth: Int,
        depthHeight: Int,
        calibration: AVCameraCalibrationData? = nil
    ) {
        self.videoWidth = max(1, videoWidth)
        self.videoHeight = max(1, videoHeight)
        self.depthWidth = max(1, depthWidth)
        self.depthHeight = max(1, depthHeight)

        if let calibration {
            let reference = calibration.intrinsicMatrixReferenceDimensions
            let refWidth = max(1, Double(reference.width))
            let refHeight = max(1, Double(reference.height))
            // Intrinsics describe the full sensor space; depth is delivered on a
            // smaller grid that still shares the same optical axis and distortion.
            depthScaleX = (refWidth / Double(self.videoWidth)) * (Double(self.depthWidth) / refWidth)
            depthScaleY = (refHeight / Double(self.videoHeight)) * (Double(self.depthHeight) / refHeight)
        } else {
            depthScaleX = Double(self.depthWidth) / Double(self.videoWidth)
            depthScaleY = Double(self.depthHeight) / Double(self.videoHeight)
        }
    }

    /// Normalized depth UV in `0...1` for a video pixel, optionally mirrored on X.
    func depthUV(videoX: Int, videoY: Int, mirrorX: Bool) -> (u: Double, v: Double) {
        let srcX = mirrorX ? (videoWidth - 1 - videoX) : videoX
        let depthX = Double(srcX) * depthScaleX
        let depthY = Double(videoY) * depthScaleY
        let u = depthX / Double(max(1, depthWidth - 1))
        let v = depthY / Double(max(1, depthHeight - 1))
        return (
            min(1, max(0, u)),
            min(1, max(0, v))
        )
    }
}
