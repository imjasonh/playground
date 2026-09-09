import CoreGraphics
import Foundation
import Vision

/// Pose points used only to reshape a source face into a destination outline.
/// The write region is the model outline, not a Vision rectangle.
enum FaceSwapLandmarks {
    static func locate(raster: FaceSwapRaster) -> [FaceSwapLandmarkTrio] {
        guard let cgImage = raster.makeCGImage() else { return [] }
        let handler = VNImageRequestHandler(cgImage: cgImage, orientation: .up, options: [:])
        let request = VNDetectFaceLandmarksRequest()
        do {
            try handler.perform([request])
        } catch {
            return []
        }
        let imageSize = CGSize(width: raster.width, height: raster.height)
        var trios: [FaceSwapLandmarkTrio] = []
        for observation in request.results ?? [] {
            guard let left = average(
                observation.landmarks?.leftPupil,
                fallback: observation.landmarks?.leftEye,
                faceBox: observation.boundingBox,
                imageSize: imageSize
            ), let right = average(
                observation.landmarks?.rightPupil,
                fallback: observation.landmarks?.rightEye,
                faceBox: observation.boundingBox,
                imageSize: imageSize
            ), let mouth = average(
                observation.landmarks?.outerLips,
                fallback: observation.landmarks?.innerLips,
                faceBox: observation.boundingBox,
                imageSize: imageSize
            ) else {
                continue
            }
            trios.append(FaceSwapLandmarkTrio(leftEye: left, rightEye: right, mouth: mouth))
        }
        return trios
    }

    static func trio(inside outline: FaceSwapOutline, candidates: [FaceSwapLandmarkTrio], width: Int, height: Int) -> FaceSwapLandmarkTrio? {
        let polygon = FaceSwapOutlineValidation.pixelPoints(outline, width: width, height: height, inset: 0)
        return candidates.first { trio in
            let center = CGPoint(
                x: (trio.leftEye.x + trio.rightEye.x) / 2,
                y: (trio.leftEye.y + trio.rightEye.y) / 2
            )
            return FaceSwapOutlineValidation.contains(center, polygon: polygon)
        }
    }

    private static func average(
        _ primary: VNFaceLandmarkRegion2D?,
        fallback: VNFaceLandmarkRegion2D?,
        faceBox: CGRect,
        imageSize: CGSize
    ) -> CGPoint? {
        let region = primary ?? fallback
        guard let region, !region.normalizedPoints.isEmpty else { return nil }
        let points = region.normalizedPoints.map { point in
            pixelPoint(visionPoint: point, faceBox: faceBox, imageSize: imageSize)
        }
        let sum = points.reduce(CGPoint.zero) { partial, point in
            CGPoint(x: partial.x + point.x, y: partial.y + point.y)
        }
        let count = CGFloat(points.count)
        return CGPoint(x: sum.x / count, y: sum.y / count)
    }

    private static func pixelPoint(visionPoint: CGPoint, faceBox: CGRect, imageSize: CGSize) -> CGPoint {
        let visionX = faceBox.origin.x + visionPoint.x * faceBox.width
        let visionY = faceBox.origin.y + visionPoint.y * faceBox.height
        return CGPoint(x: visionX * imageSize.width, y: (1 - visionY) * imageSize.height)
    }
}
