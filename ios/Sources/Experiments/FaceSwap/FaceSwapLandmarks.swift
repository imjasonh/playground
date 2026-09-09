import CoreGraphics
import Foundation
import Vision

/// A face-skin contour read from the photo, before the model assigns roles.
struct FaceSwapCandidate: Equatable, Sendable {
    var id: String
    var points: [CGPoint]
    var place: String
    /// How much darker the chin is than the cheek. A lighting statistic, not a person label.
    var chinContrast: Double
}

/// Pose points used only to reshape a source face into a destination outline.
/// The write region is a face contour, not a Vision rectangle.
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

    /// Face-skin contours for the iOS 26 model. The model cannot see the photo,
    /// so it chooses among these contours by id. Bounding boxes are not returned.
    static func candidates(raster: FaceSwapRaster) -> [FaceSwapCandidate] {
        guard let cgImage = raster.makeCGImage() else { return [] }
        let handler = VNImageRequestHandler(cgImage: cgImage, orientation: .up, options: [:])
        let request = VNDetectFaceLandmarksRequest()
        do {
            try handler.perform([request])
        } catch {
            return []
        }
        var found: [FaceSwapCandidate] = []
        for (index, observation) in (request.results ?? []).enumerated() {
            guard let landmarks = observation.landmarks else { continue }
            let jawRegion = landmarks.faceContour
                ?? landmarks.medianLine
            let jawPoints: [CGPoint]
            if let jawRegion, !jawRegion.normalizedPoints.isEmpty {
                jawPoints = topLeftPoints(jawRegion, faceBox: observation.boundingBox)
            } else {
                jawPoints = [landmarks.leftEyebrow, landmarks.rightEyebrow, landmarks.nose, landmarks.outerLips]
                    .compactMap { $0 }
                    .flatMap { topLeftPoints($0, faceBox: observation.boundingBox) }
            }
            guard jawPoints.count >= 4 else { continue }
            let brows = [landmarks.leftEyebrow, landmarks.rightEyebrow]
                .compactMap { $0 }
                .flatMap { topLeftPoints($0, faceBox: observation.boundingBox) }
            let closed = FaceSwapContours.closeJaw(jawPoints, brows: brows)
            let points = FaceSwapContours.decimate(closed, limit: 16)
            let outline = FaceSwapOutline(id: "face-\(index + 1)", role: .source, refersTo: "", points: points)
            if FaceSwapOutlineValidation.check(outline) != nil { continue }
            let bounds = FaceSwapOutlineValidation.boundsOf(points)
            let center = CGPoint(x: bounds.midX, y: bounds.midY)
            found.append(
                FaceSwapCandidate(
                    id: outline.id,
                    points: points,
                    place: FaceSwapContours.place(for: center),
                    chinContrast: chinContrast(raster: raster, jaw: jawPoints, faceBox: observation.boundingBox)
                )
            )
        }
        let ranked = found.sorted {
            let left = FaceSwapOutlineValidation.boundsOf($0.points)
            let right = FaceSwapOutlineValidation.boundsOf($1.points)
            return left.width * left.height > right.width * right.height
        }
        return ranked.prefix(6).enumerated().map { offset, candidate in
            var copy = candidate
            copy.id = "face-\(offset + 1)"
            return copy
        }
    }

    private static func topLeftPoints(_ region: VNFaceLandmarkRegion2D, faceBox: CGRect) -> [CGPoint] {
        region.normalizedPoints.map { point in
            let visionX = faceBox.origin.x + point.x * faceBox.width
            let visionY = faceBox.origin.y + point.y * faceBox.height
            return CGPoint(
                x: min(1, max(0, visionX)),
                y: min(1, max(0, 1 - visionY))
            )
        }
    }

    private static func chinContrast(raster: FaceSwapRaster, jaw: [CGPoint], faceBox: CGRect) -> Double {
        guard let lowest = jaw.max(by: { $0.y < $1.y }) else { return 0 }
        let chin = sampleLuma(raster, normalized: lowest)
        let cheek = sampleLuma(
            raster,
            normalized: CGPoint(x: faceBox.midX, y: 1 - (faceBox.midY + faceBox.height * 0.15))
        )
        guard cheek > 1 else { return 0 }
        return min(1, max(0, (cheek - chin) / cheek))
    }

    private static func sampleLuma(_ raster: FaceSwapRaster, normalized: CGPoint) -> Double {
        let x = min(raster.width - 1, max(0, Int((normalized.x * CGFloat(raster.width)).rounded())))
        let y = min(raster.height - 1, max(0, Int((normalized.y * CGFloat(raster.height)).rounded())))
        guard let color = raster.rgb(x: x, y: y) else { return 0 }
        return 0.2126 * Double(color.0) + 0.7152 * Double(color.1) + 0.0722 * Double(color.2)
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
