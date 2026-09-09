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

/// Reconstructs a face inside the destination outline only.
///
/// The model supplies the outline and the recipe. This writes source identity
/// under destination light, then feathers inward. It does not copy a rectangle
/// of source pixels. Pixels outside the write polygon stay byte-identical.
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
        let affine = landmarkAffine(source: sourceLandmarks, destination: destinationLandmarks)
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
            affine: affine,
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
                    affine: affine
                )
                let mappedPoint = CGPoint(x: mapped.0, y: mapped.1)
                guard FaceSwapOutlineValidation.contains(mappedPoint, polygon: sourcePolygon),
                      let sample = sampleBilinear(original, x: mapped.0, y: mapped.1)
                else {
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
            warp: affine == nil ? "outline" : "pose"
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

    private static func mapPoint(
        _ dest: (Double, Double),
        fitPose: Double,
        sourceBounds: CGRect,
        destBounds: CGRect,
        affine: ((Double, Double, Double), (Double, Double, Double))?
    ) -> (Double, Double) {
        let boxed = mapThroughBounds(dest, sourceBounds: sourceBounds, destBounds: destBounds)
        guard let affine, fitPose > 0 else { return boxed }
        let posed = (
            affine.0.0 * dest.0 + affine.0.1 * dest.1 + affine.0.2,
            affine.1.0 * dest.0 + affine.1.1 * dest.1 + affine.1.2
        )
        return (
            boxed.0 + (posed.0 - boxed.0) * fitPose,
            boxed.1 + (posed.1 - boxed.1) * fitPose
        )
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

    private static func landmarkAffine(
        source: FaceSwapLandmarkTrio?,
        destination: FaceSwapLandmarkTrio?
    ) -> ((Double, Double, Double), (Double, Double, Double))? {
        guard let source, let destination else { return nil }
        return affineDestToSource(
            dest: (destination.leftEye, destination.rightEye, destination.mouth),
            source: (source.leftEye, source.rightEye, source.mouth)
        )
    }

    private static func affineDestToSource(
        dest: (CGPoint, CGPoint, CGPoint),
        source: (CGPoint, CGPoint, CGPoint)
    ) -> ((Double, Double, Double), (Double, Double, Double))? {
        let a = Double(dest.0.x)
        let b = Double(dest.0.y)
        let c = Double(dest.1.x)
        let d = Double(dest.1.y)
        let e = Double(dest.2.x)
        let f = Double(dest.2.y)
        let det = a * (d - f) - b * (c - e) + (c * f - e * d)
        if abs(det) < 1 { return nil }
        func solve(_ y0: Double, _ y1: Double, _ y2: Double) -> (Double, Double, Double) {
            let aCoef = (y0 * (d - f) - b * (y1 - y2) + (y1 * f - y2 * d)) / det
            let bCoef = (a * (y1 - y2) - y0 * (c - e) + (c * y2 - e * y1)) / det
            let cCoef = (a * (d * y2 - f * y1) - b * (c * y2 - e * y1) + y0 * (c * f - e * d)) / det
            return (aCoef, bCoef, cCoef)
        }
        return (
            solve(Double(source.0.x), Double(source.1.x), Double(source.2.x)),
            solve(Double(source.0.y), Double(source.1.y), Double(source.2.y))
        )
    }

    /// Places source color ratios under destination light, then adds a little source detail.
    /// A raw copy of `source` is the stamp this avoids when lightingMatch is above 0.
    private static func reconstruct(
        source: (UInt8, UInt8, UInt8),
        destination: (UInt8, UInt8, UInt8),
        sourceMean: (Double, Double, Double),
        destMean: (Double, Double, Double),
        plan: FaceSwapEditPlan
    ) -> (UInt8, UInt8, UInt8) {
        let sourceLuma = luma(source)
        let destinationLuma = luma(destination)
        let light = sourceLuma + (destinationLuma - sourceLuma) * plan.lightingMatch
        func channel(_ sourceValue: UInt8, _ destValue: UInt8, _ sourceMean: Double, _ destMean: Double) -> UInt8 {
            let sourceChannel = Double(sourceValue)
            let chroma = sourceLuma > 1 ? sourceChannel / sourceLuma : sourceChannel / 255
            var value = chroma * light
            let meanGain = sourceMean > 1 ? destMean / sourceMean : 1
            let meanLit = sourceChannel * (1 + (meanGain - 1) * plan.lightingMatch)
            value = value * 0.7 + meanLit * 0.3
            value += (Double(destValue) - value) * plan.colorMatch * 0.35
            let detail = sourceChannel - sourceLuma
            value += detail * plan.detailTransfer * 0.35
            return UInt8(min(255, max(0, value.rounded())))
        }
        return (
            channel(source.0, destination.0, sourceMean.0, destMean.0),
            channel(source.1, destination.1, sourceMean.1, destMean.1),
            channel(source.2, destination.2, sourceMean.2, destMean.2)
        )
    }

    private static func luma(_ color: (UInt8, UInt8, UInt8)) -> Double {
        0.2126 * Double(color.0) + 0.7152 * Double(color.1) + 0.0722 * Double(color.2)
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
        affine: ((Double, Double, Double), (Double, Double, Double))?,
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
                    affine: affine
                )
                let point = CGPoint(x: mapped.0, y: mapped.1)
                guard FaceSwapOutlineValidation.contains(point, polygon: sourcePolygon),
                      let sample = sampleBilinear(original, x: mapped.0, y: mapped.1)
                else {
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
