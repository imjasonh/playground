import CoreGraphics
import Foundation

struct FaceSwapLandmarkTrio: Equatable, Sendable {
    var leftEye: CGPoint
    var rightEye: CGPoint
    var mouth: CGPoint
}

struct FaceSwapPasteOutput: Equatable, Sendable {
    var image: FaceSwapRaster
    var mask: [UInt8]
    var stats: FaceSwapEditStats
}

/// Places a source face inside the destination outline only.
///
/// Eyes and mouth land on the destination eyes and mouth when landmarks exist.
/// The source face pixels are copied, then shifted toward the destination's
/// average color. Destination shading is not painted over the new face, which
/// is what turns features into a smear. A thin seam feathers the edge. Pixels
/// outside the write polygon stay byte-identical.
enum FaceSwapEditor {
    static func apply(
        plan: FaceSwapEditPlan,
        source: FaceSwapOutline,
        destination: FaceSwapOutline,
        original: FaceSwapRaster,
        working: FaceSwapRaster,
        sourceLandmarks: FaceSwapLandmarkTrio?,
        destinationLandmarks: FaceSwapLandmarkTrio?
    ) -> Result<FaceSwapPasteOutput, FaceSwapMessageError> {
        guard original.width == working.width, original.height == working.height, original.width > 0 else {
            return .failure("Source and working images differ in size.")
        }
        let recipe = plan.clamped()
        let width = working.width
        let height = working.height
        let sourcePolygon = FaceSwapOutlineValidation.pixelPoints(source, width: width, height: height, inset: 0)
        let destinationPolygon = writePolygon(destination: destination, plan: recipe, width: width, height: height)
        let mask = FaceSwapOutlineValidation.mask(polygon: destinationPolygon, width: width, height: height)
        let maskPixels = mask.reduce(0) { $0 + ($1 > 0 ? 1 : 0) }
        guard maskPixels > 0 else {
            return .failure("Destination outline has an empty write region.")
        }

        let sourceBounds = FaceSwapOutlineValidation.boundsOf(sourcePolygon)
        let destBounds = FaceSwapOutlineValidation.boundsOf(destinationPolygon)
        let placement = facePlacement(source: sourceLandmarks, destination: destinationLandmarks)
        let sourceCenter = CGPoint(x: sourceBounds.midX, y: sourceBounds.midY)
        let band = edgeBandPixels(plan: recipe, bounds: destBounds)
        let destMean = meanColor(original, mask: mask, width: width)
        let sourceMean = meanMappedColor(
            original: original,
            mask: mask,
            width: width,
            height: height,
            sourcePolygon: sourcePolygon,
            sourceBounds: sourceBounds,
            destBounds: destBounds,
            placement: placement,
            fitPose: recipe.fitPose
        )

        var output = working.copy()
        var written = 0
        for y in 0..<height {
            for x in 0..<width {
                let maskIndex = y * width + x
                if mask[maskIndex] == 0 { continue }
                let destPoint = (Double(x) + 0.5, Double(y) + 0.5)
                let mapped = mapPoint(
                    destPoint,
                    fitPose: recipe.fitPose,
                    sourceBounds: sourceBounds,
                    destBounds: destBounds,
                    placement: placement
                )
                guard let mappedPoint = samplePointInsideFace(
                    CGPoint(x: mapped.0, y: mapped.1),
                    polygon: sourcePolygon,
                    center: sourceCenter
                ), let sample = sampleBilinear(original, x: mappedPoint.x, y: mappedPoint.y) else {
                    continue
                }
                guard let destinationColor = original.rgb(x: x, y: y) else { continue }
                let adapted = reconstruct(
                    source: sample,
                    destination: destinationColor,
                    sourceMean: sourceMean,
                    destMean: destMean,
                    plan: recipe
                )
                let seam = seamWeight(x: x, y: y, mask: mask, width: width, height: height, band: band)
                if seam <= 0 { continue }
                let offset = maskIndex * 4
                let kept = output.rgba
                output.rgba[offset] = mix(adapted.0, kept[offset], seam)
                output.rgba[offset + 1] = mix(adapted.1, kept[offset + 1], seam)
                output.rgba[offset + 2] = mix(adapted.2, kept[offset + 2], seam)
                output.rgba[offset + 3] = 255
                written += 1
            }
        }
        guard written > 0 else {
            return .failure("The edit wrote 0 pixels inside the destination outline.")
        }

        let outside = pixelsChangedOutsideMask(before: working, after: output, mask: mask)
        let stats = FaceSwapEditStats(
            sourceID: source.id,
            destinationID: destination.id,
            writtenPixels: written,
            changedFromOriginal: FaceSwapDiff.changedPixelCount(original: original, edited: output),
            totalPixels: original.pixelCount,
            outsideMaskChanged: outside,
            warp: placement == nil ? "outline" : "eyes"
        )
        return .success(FaceSwapPasteOutput(image: output, mask: mask, stats: stats))
    }

    static func resultMessage(_ stats: FaceSwapEditStats, plan: FaceSwapEditPlan) -> String {
        let recipe = plan.clamped()
        let why = recipe.motive.isEmpty ? "" : " \(recipe.motive)"
        return "Reconstructed \(stats.destinationID) from \(stats.sourceID) (\(stats.warp)).\(why) "
            + String(
                format: "fit=%.2f light=%.2f color=%.2f detail=%.2f edge=%.2f inset=%.2f. ",
                recipe.fitPose,
                recipe.lightingMatch,
                recipe.colorMatch,
                recipe.detailTransfer,
                recipe.edgeBand,
                recipe.inset
            )
            + "Wrote \(stats.writtenPixels) outline pixels. "
            + "\(stats.outsideMaskChanged) pixels outside the outline changed."
    }

    private static func writePolygon(
        destination: FaceSwapOutline,
        plan: FaceSwapEditPlan,
        width: Int,
        height: Int
    ) -> [CGPoint] {
        if let tightened = FaceSwapOutlineValidation.acceptedTightening(
            base: destination.points,
            tightened: plan.tightenedDestination
        ) {
            let outline = FaceSwapOutline(
                id: destination.id,
                role: destination.role,
                refersTo: destination.refersTo,
                points: tightened
            )
            return FaceSwapOutlineValidation.pixelPoints(outline, width: width, height: height, inset: 0)
        }
        return FaceSwapOutlineValidation.pixelPoints(destination, width: width, height: height, inset: plan.inset)
    }

    private static func edgeBandPixels(plan: FaceSwapEditPlan, bounds: CGRect) -> Int {
        let shorter = min(bounds.width, bounds.height)
        let pixels = shorter * CGFloat(plan.edgeBand)
        return min(24, max(2, Int(pixels.rounded())))
    }

    private static func seamWeight(x: Int, y: Int, mask: [UInt8], width: Int, height: Int, band: Int) -> Double {
        var nearest = band
        let minY = max(0, y - band)
        let maxY = min(height - 1, y + band)
        let minX = max(0, x - band)
        let maxX = min(width - 1, x + band)
        for sampleY in minY...maxY {
            for sampleX in minX...maxX {
                if mask[sampleY * width + sampleX] == 0 {
                    let distance = max(abs(sampleX - x), abs(sampleY - y))
                    nearest = min(nearest, distance)
                }
            }
        }
        if band <= 0 { return 1 }
        return min(1, max(0, Double(nearest) / Double(band)))
    }

    /// Eye line plus mouth distance. A full three-point affine shears the face into a smear.
    private struct FacePlacement {
        var sourceCenter: CGPoint
        var destCenter: CGPoint
        var sourceAngle: Double
        var destAngle: Double
        var scaleX: Double
        var scaleY: Double
    }

    private static func facePlacement(
        source: FaceSwapLandmarkTrio?,
        destination: FaceSwapLandmarkTrio?
    ) -> FacePlacement? {
        guard let source, let destination else { return nil }
        let sourceCenter = midpoint(source.leftEye, source.rightEye)
        let destCenter = midpoint(destination.leftEye, destination.rightEye)
        let sourceEye = max(1, hypot(source.rightEye.x - source.leftEye.x, source.rightEye.y - source.leftEye.y))
        let destEye = max(1, hypot(destination.rightEye.x - destination.leftEye.x, destination.rightEye.y - destination.leftEye.y))
        let sourceMouth = max(1, hypot(source.mouth.x - sourceCenter.x, source.mouth.y - sourceCenter.y))
        let destMouth = max(1, hypot(destination.mouth.x - destCenter.x, destination.mouth.y - destCenter.y))
        let scaleX = Double(sourceEye / destEye)
        var scaleY = Double(sourceMouth / destMouth)
        guard scaleX.isFinite, scaleX >= 0.45, scaleX <= 2.2 else { return nil }
        if !scaleY.isFinite || scaleY < 0.45 || scaleY > 2.2 {
            scaleY = scaleX
        }
        return FacePlacement(
            sourceCenter: sourceCenter,
            destCenter: destCenter,
            sourceAngle: Double(atan2(source.rightEye.y - source.leftEye.y, source.rightEye.x - source.leftEye.x)),
            destAngle: Double(atan2(destination.rightEye.y - destination.leftEye.y, destination.rightEye.x - destination.leftEye.x)),
            scaleX: scaleX,
            scaleY: scaleY
        )
    }

    private static func midpoint(_ left: CGPoint, _ right: CGPoint) -> CGPoint {
        CGPoint(x: (left.x + right.x) / 2, y: (left.y + right.y) / 2)
    }

    private static func mapPoint(
        _ dest: (Double, Double),
        fitPose: Double,
        sourceBounds: CGRect,
        destBounds: CGRect,
        placement: FacePlacement?
    ) -> (Double, Double) {
        let boxed = mapThroughBounds(dest, sourceBounds: sourceBounds, destBounds: destBounds)
        guard let placement, fitPose > 0 else { return boxed }
        let dx = dest.0 - Double(placement.destCenter.x)
        let dy = dest.1 - Double(placement.destCenter.y)
        let cosDest = cos(-placement.destAngle)
        let sinDest = sin(-placement.destAngle)
        let uprightX = dx * cosDest - dy * sinDest
        let uprightY = dx * sinDest + dy * cosDest
        let scaledX = uprightX * placement.scaleX
        let scaledY = uprightY * placement.scaleY
        let cosSource = cos(placement.sourceAngle)
        let sinSource = sin(placement.sourceAngle)
        let posed = (
            Double(placement.sourceCenter.x) + scaledX * cosSource - scaledY * sinSource,
            Double(placement.sourceCenter.y) + scaledX * sinSource + scaledY * cosSource
        )
        return (
            boxed.0 + (posed.0 - boxed.0) * fitPose,
            boxed.1 + (posed.1 - boxed.1) * fitPose
        )
    }

    /// Keeps a sample on the source face so the destination is not left as holes of the old face.
    private static func samplePointInsideFace(_ point: CGPoint, polygon: [CGPoint], center: CGPoint) -> CGPoint? {
        if FaceSwapOutlineValidation.contains(point, polygon: polygon) { return point }
        var best: CGPoint?
        var low = 0.0
        var high = 1.0
        for _ in 0..<8 {
            let t = (low + high) / 2
            let candidate = CGPoint(
                x: point.x + (center.x - point.x) * t,
                y: point.y + (center.y - point.y) * t
            )
            if FaceSwapOutlineValidation.contains(candidate, polygon: polygon) {
                best = candidate
                high = t
            } else {
                low = t
            }
        }
        return best
    }

    private static func mapThroughBounds(
        _ dest: (Double, Double),
        sourceBounds: CGRect,
        destBounds: CGRect
    ) -> (Double, Double) {
        let scaleX = destBounds.width > 1 ? sourceBounds.width / destBounds.width : 1
        let scaleY = destBounds.height > 1 ? sourceBounds.height / destBounds.height : 1
        return (
            Double(sourceBounds.minX) + (dest.0 - Double(destBounds.minX)) * Double(scaleX),
            Double(sourceBounds.minY) + (dest.1 - Double(destBounds.minY)) * Double(scaleY)
        )
    }

    /// Shifts the source face toward the destination's average color.
    ///
    /// Each destination pixel's own shading is not used as the new face's light.
    /// That replacement is what smears eyes and mouth. Local contrast stays with
    /// the source face. A raw copy is the result when lightingMatch is 0.
    private static func reconstruct(
        source: (UInt8, UInt8, UInt8),
        destination: (UInt8, UInt8, UInt8),
        sourceMean: (Double, Double, Double),
        destMean: (Double, Double, Double),
        plan: FaceSwapEditPlan
    ) -> (UInt8, UInt8, UInt8) {
        func channel(_ sourceValue: UInt8, _ destValue: UInt8, _ sourceMean: Double, _ destMean: Double) -> UInt8 {
            let sourceChannel = Double(sourceValue)
            let local = sourceChannel - sourceMean
            let shiftedMean = sourceMean + (destMean - sourceMean) * plan.lightingMatch
            let contrast = max(plan.detailTransfer, 1 - plan.lightingMatch)
            var value = shiftedMean + local * contrast
            if plan.colorMatch > 0 {
                value += (Double(destValue) - value) * plan.colorMatch * 0.35
            }
            return UInt8(min(255, max(0, value.rounded())))
        }
        return (
            channel(source.0, destination.0, sourceMean.0, destMean.0),
            channel(source.1, destination.1, sourceMean.1, destMean.1),
            channel(source.2, destination.2, sourceMean.2, destMean.2)
        )
    }

    private static func meanColor(_ raster: FaceSwapRaster, mask: [UInt8], width: Int) -> (Double, Double, Double) {
        var sums = (0.0, 0.0, 0.0)
        var count = 0
        for index in mask.indices where mask[index] > 0 {
            let offset = index * 4
            sums.0 += Double(raster.rgba[offset])
            sums.1 += Double(raster.rgba[offset + 1])
            sums.2 += Double(raster.rgba[offset + 2])
            count += 1
        }
        guard count > 0 else { return (128, 128, 128) }
        let n = Double(count)
        return (sums.0 / n, sums.1 / n, sums.2 / n)
    }

    private static func meanMappedColor(
        original: FaceSwapRaster,
        mask: [UInt8],
        width: Int,
        height: Int,
        sourcePolygon: [CGPoint],
        sourceBounds: CGRect,
        destBounds: CGRect,
        placement: FacePlacement?,
        fitPose: Double
    ) -> (Double, Double, Double) {
        var sums = (0.0, 0.0, 0.0)
        var count = 0
        let step = max(1, Int(sqrt(Double(max(1, mask.reduce(0) { $0 + ($1 > 0 ? 1 : 0) }))) / 12))
        for y in stride(from: 0, to: height, by: step) {
            for x in stride(from: 0, to: width, by: step) {
                if mask[y * width + x] == 0 { continue }
                let mapped = mapPoint(
                    (Double(x) + 0.5, Double(y) + 0.5),
                    fitPose: fitPose,
                    sourceBounds: sourceBounds,
                    destBounds: destBounds,
                    placement: placement
                )
                let center = CGPoint(x: sourceBounds.midX, y: sourceBounds.midY)
                guard let point = samplePointInsideFace(
                    CGPoint(x: mapped.0, y: mapped.1),
                    polygon: sourcePolygon,
                    center: center
                ), let sample = sampleBilinear(original, x: point.x, y: point.y) else {
                    continue
                }
                sums.0 += Double(sample.0)
                sums.1 += Double(sample.1)
                sums.2 += Double(sample.2)
                count += 1
            }
        }
        guard count > 0 else { return (128, 128, 128) }
        let n = Double(count)
        return (sums.0 / n, sums.1 / n, sums.2 / n)
    }

    private static func sampleBilinear(_ raster: FaceSwapRaster, x: Double, y: Double) -> (UInt8, UInt8, UInt8)? {
        guard raster.width > 1, raster.height > 1 else { return nil }
        if x < 0 || y < 0 || x >= Double(raster.width - 1) || y >= Double(raster.height - 1) {
            return nil
        }
        let x0 = Int(x)
        let y0 = Int(y)
        let tx = x - Double(x0)
        let ty = y - Double(y0)
        func channel(_ channel: Int) -> UInt8 {
            let i00 = (y0 * raster.width + x0) * 4 + channel
            let i10 = (y0 * raster.width + x0 + 1) * 4 + channel
            let i01 = ((y0 + 1) * raster.width + x0) * 4 + channel
            let i11 = ((y0 + 1) * raster.width + x0 + 1) * 4 + channel
            let top = Double(raster.rgba[i00]) * (1 - tx) + Double(raster.rgba[i10]) * tx
            let bottom = Double(raster.rgba[i01]) * (1 - tx) + Double(raster.rgba[i11]) * tx
            let value = top * (1 - ty) + bottom * ty
            return UInt8(min(255, max(0, value.rounded())))
        }
        return (channel(0), channel(1), channel(2))
    }

    private static func mix(_ edited: UInt8, _ original: UInt8, _ weight: Double) -> UInt8 {
        let value = Double(edited) * weight + Double(original) * (1 - weight)
        return UInt8(min(255, max(0, value.rounded())))
    }

    private static func pixelsChangedOutsideMask(before: FaceSwapRaster, after: FaceSwapRaster, mask: [UInt8]) -> Int {
        var count = 0
        for pixel in 0..<before.pixelCount {
            if mask[pixel] > 0 { continue }
            let offset = pixel * 4
            if before.rgba[offset] != after.rgba[offset]
                || before.rgba[offset + 1] != after.rgba[offset + 1]
                || before.rgba[offset + 2] != after.rgba[offset + 2]
            {
                count += 1
            }
        }
        return count
    }
}
