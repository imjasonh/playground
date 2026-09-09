import CoreGraphics
import CoreVideo
import Foundation
import Vision

/// A face or person the model can name. Tools may only write inside these regions.
struct FaceSwapRegion: Equatable, Sendable {
    enum Kind: String, Equatable, Sendable {
        case face
        case person
    }

    var id: String
    var kind: Kind
    var place: String
    var colorName: String
    /// Closed contour for the overlay. The write mask can be tighter than this.
    var points: [CGPoint]
    /// Person pixels only. Nil means the polygon is the write region.
    var mask: [UInt8]?
    var onID: String?

    func outline(refersTo: String, role: FaceSwapOutline.Role) -> FaceSwapOutline {
        FaceSwapOutline(id: id, role: role, refersTo: refersTo, points: points)
    }
}

enum FaceSwapRegions {
    static let maximumRegionFraction = 0.45

    static func detect(raster: FaceSwapRaster) -> [FaceSwapRegion] {
        var regions: [FaceSwapRegion] = []
        let people = personRegions(raster: raster)
        regions.append(contentsOf: people)
        for candidate in FaceSwapLandmarks.candidates(raster: raster) {
            let bounds = FaceSwapOutlineValidation.boundsOf(candidate.points)
            let center = CGPoint(x: bounds.midX, y: bounds.midY)
            let onPerson = people.first { regionContains($0, point: center, width: raster.width, height: raster.height) }
            regions.append(
                FaceSwapRegion(
                    id: candidate.id,
                    kind: .face,
                    place: candidate.place,
                    colorName: colorName(sample: meanColor(raster: raster, polygon: candidate.points)),
                    points: candidate.points,
                    mask: nil,
                    onID: onPerson?.id
                )
            )
        }
        return regions
    }

    static func catalog(_ regions: [FaceSwapRegion]) -> String {
        var lines = [
            "Regions already found. Tools may use these ids only. A tool cannot grow a region or touch pixels outside it.",
            "kind=face is a skin contour. kind=person is that person's pixels, not the background around them."
        ]
        for region in regions.prefix(12) {
            let bounds = FaceSwapOutlineValidation.boundsOf(region.points)
            var line = "id=\(region.id) kind=\(region.kind.rawValue) place=\(region.place) color=\(region.colorName) "
            line += String(format: "bounds=%.2f,%.2f %.2fx%.2f", bounds.minX, bounds.minY, bounds.width, bounds.height)
            if let onID = region.onID {
                line += " on=\(onID)"
            }
            if region.mask == nil, region.kind == .person {
                line += " shape=box"
            }
            lines.append(line)
        }
        lines.append("removeRegion erases one region. copyRegion adds copies at new centers. replaceFaces copies one face onto other face ids.")
        return AgentContextBudget.truncateToChars(lines.joined(separator: "\n"), maxChars: 1_200)
    }

    static func region(id: String, in regions: [FaceSwapRegion]) -> FaceSwapRegion? {
        let key = id.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        return regions.first { $0.id.lowercased() == key }
    }

    static func writeMask(_ region: FaceSwapRegion, width: Int, height: Int, inset: Double) -> [UInt8] {
        var mask: [UInt8]
        if let stored = region.mask, stored.count == width * height {
            mask = stored
        } else {
            let polygon = FaceSwapOutlineValidation.pixelPoints(
                region.outline(refersTo: "", role: .destination),
                width: width,
                height: height,
                inset: 0
            )
            mask = FaceSwapOutlineValidation.mask(polygon: polygon, width: width, height: height)
        }
        let eroded = erode(mask, width: width, height: height, inset: inset)
        return eroded
    }

    static func fraction(_ mask: [UInt8]) -> Double {
        guard !mask.isEmpty else { return 0 }
        let filled = mask.reduce(0) { $0 + ($1 > 0 ? 1 : 0) }
        return Double(filled) / Double(mask.count)
    }

    static func colorName(sample: (Double, Double, Double)) -> String {
        let red = sample.0
        let green = sample.1
        let blue = sample.2
        let maxChannel = max(red, green, blue)
        let minChannel = min(red, green, blue)
        if maxChannel < 45 { return "black" }
        if minChannel > 200 && maxChannel - minChannel < 30 { return "white" }
        if maxChannel - minChannel < 25 { return "gray" }
        if blue > red + 18 && blue > green + 8 { return "blue" }
        if red > green + 18 && red > blue + 18 { return "red" }
        if green > red + 12 && green > blue + 12 { return "green" }
        if red > 150 && green > 120 && blue < 110 { return "yellow" }
        if red > 140 && green > 90 && blue < 100 { return "orange" }
        if red > 90 && green > 70 && blue > 60 && abs(red - green) < 40 { return "tan" }
        return "mixed"
    }

    static func meanColor(raster: FaceSwapRaster, polygon: [CGPoint]) -> (Double, Double, Double) {
        let mask = FaceSwapOutlineValidation.mask(
            polygon: FaceSwapOutlineValidation.pixelPoints(
                FaceSwapOutline(id: "sample", role: .source, refersTo: "", points: polygon),
                width: raster.width,
                height: raster.height,
                inset: 0
            ),
            width: raster.width,
            height: raster.height
        )
        return meanColor(raster: raster, mask: mask)
    }

    private static func personRegions(raster: FaceSwapRaster) -> [FaceSwapRegion] {
        guard let cgImage = raster.makeCGImage() else { return [] }
        let handler = VNImageRequestHandler(cgImage: cgImage, orientation: .up, options: [:])
        let request = VNDetectHumanRectanglesRequest()
        do {
            try handler.perform([request])
        } catch {
            return []
        }
        let boxes = (request.results ?? []).map { topLeftRect($0.boundingBox) }
        guard !boxes.isEmpty else { return [] }
        let segmentation = personMask(handler: handler, width: raster.width, height: raster.height)
        var regions: [FaceSwapRegion] = []
        for (index, box) in boxes.prefix(6).enumerated() {
            let mask = instanceMask(
                segmentation: segmentation,
                box: box,
                boxes: boxes,
                width: raster.width,
                height: raster.height
            )
            let filled = mask.reduce(0) { $0 + ($1 > 0 ? 1 : 0) }
            guard filled > 16 else { continue }
            let points = polygon(for: box)
            let color = colorName(sample: shirtColor(raster: raster, mask: mask, box: box))
            let center = CGPoint(x: box.midX, y: box.midY)
            regions.append(
                FaceSwapRegion(
                    id: "person-\(index + 1)",
                    kind: .person,
                    place: FaceSwapContours.place(for: center),
                    colorName: color,
                    points: points,
                    mask: segmentation == nil ? nil : mask,
                    onID: nil
                )
            )
        }
        return regions
    }

    private static func instanceMask(
        segmentation: [UInt8]?,
        box: CGRect,
        boxes: [CGRect],
        width: Int,
        height: Int
    ) -> [UInt8] {
        var mask = [UInt8](repeating: 0, count: width * height)
        let minX = max(0, Int((box.minX * CGFloat(width)).rounded(.down)))
        let maxX = min(width - 1, Int((box.maxX * CGFloat(width)).rounded(.up)))
        let minY = max(0, Int((box.minY * CGFloat(height)).rounded(.down)))
        let maxY = min(height - 1, Int((box.maxY * CGFloat(height)).rounded(.up)))
        guard minX <= maxX, minY <= maxY else { return mask }
        for y in minY...maxY {
            for x in minX...maxX {
                let nx = (CGFloat(x) + 0.5) / CGFloat(width)
                let ny = (CGFloat(y) + 0.5) / CGFloat(height)
                if let segmentation {
                    if segmentation[y * width + x] == 0 { continue }
                    let closest = boxes.min { left, right in
                        hypot(nx - left.midX, ny - left.midY) < hypot(nx - right.midX, ny - right.midY)
                    }
                    if let closest, hypot(nx - closest.midX, ny - closest.midY) + 0.0001 < hypot(nx - box.midX, ny - box.midY) {
                        continue
                    }
                }
                mask[y * width + x] = 255
            }
        }
        return mask
    }

    private static func personMask(handler: VNImageRequestHandler, width: Int, height: Int) -> [UInt8]? {
        let request = VNGeneratePersonSegmentationRequest()
        request.qualityLevel = .balanced
        request.outputPixelFormat = kCVPixelFormatType_OneComponent8
        do {
            try handler.perform([request])
        } catch {
            return nil
        }
        guard let buffer = request.results?.first?.pixelBuffer else { return nil }
        return scaleMask(buffer, width: width, height: height)
    }

    private static func scaleMask(_ buffer: CVPixelBuffer, width: Int, height: Int) -> [UInt8]? {
        CVPixelBufferLockBaseAddress(buffer, .readOnly)
        defer { CVPixelBufferUnlockBaseAddress(buffer, .readOnly) }
        guard let base = CVPixelBufferGetBaseAddress(buffer) else { return nil }
        let sourceWidth = CVPixelBufferGetWidth(buffer)
        let sourceHeight = CVPixelBufferGetHeight(buffer)
        let rowBytes = CVPixelBufferGetBytesPerRow(buffer)
        guard sourceWidth > 0, sourceHeight > 0 else { return nil }
        let bytes = base.assumingMemoryBound(to: UInt8.self)
        var mask = [UInt8](repeating: 0, count: width * height)
        for y in 0..<height {
            let sourceY = min(sourceHeight - 1, y * sourceHeight / height)
            for x in 0..<width {
                let sourceX = min(sourceWidth - 1, x * sourceWidth / width)
                let value = bytes[sourceY * rowBytes + sourceX]
                if value > 127 {
                    mask[y * width + x] = 255
                }
            }
        }
        return mask
    }

    private static func shirtColor(raster: FaceSwapRaster, mask: [UInt8], box: CGRect) -> (Double, Double, Double) {
        let shirtMaxY = box.minY + box.height * 0.55
        var sums = (0.0, 0.0, 0.0)
        var count = 0
        for y in 0..<raster.height {
            let ny = (CGFloat(y) + 0.5) / CGFloat(raster.height)
            if ny < box.minY || ny > shirtMaxY { continue }
            for x in stride(from: 0, to: raster.width, by: 2) {
                if mask[y * raster.width + x] == 0 { continue }
                guard let color = raster.rgb(x: x, y: y) else { continue }
                sums.0 += Double(color.0)
                sums.1 += Double(color.1)
                sums.2 += Double(color.2)
                count += 1
            }
        }
        guard count > 0 else { return meanColor(raster: raster, mask: mask) }
        let n = Double(count)
        return (sums.0 / n, sums.1 / n, sums.2 / n)
    }

    private static func meanColor(raster: FaceSwapRaster, mask: [UInt8]) -> (Double, Double, Double) {
        var sums = (0.0, 0.0, 0.0)
        var count = 0
        for index in mask.indices where mask[index] > 0 {
            let offset = index * 4
            guard offset + 2 < raster.rgba.count else { continue }
            sums.0 += Double(raster.rgba[offset])
            sums.1 += Double(raster.rgba[offset + 1])
            sums.2 += Double(raster.rgba[offset + 2])
            count += 1
        }
        guard count > 0 else { return (128, 128, 128) }
        let n = Double(count)
        return (sums.0 / n, sums.1 / n, sums.2 / n)
    }

    private static func polygon(for box: CGRect) -> [CGPoint] {
        [
            CGPoint(x: box.minX, y: box.minY),
            CGPoint(x: box.midX, y: box.minY),
            CGPoint(x: box.maxX, y: box.minY),
            CGPoint(x: box.maxX, y: box.midY),
            CGPoint(x: box.maxX, y: box.maxY),
            CGPoint(x: box.midX, y: box.maxY),
            CGPoint(x: box.minX, y: box.maxY),
            CGPoint(x: box.minX, y: box.midY),
        ]
    }

    private static func topLeftRect(_ box: CGRect) -> CGRect {
        CGRect(x: box.minX, y: 1 - box.maxY, width: box.width, height: box.height)
    }

    private static func regionContains(_ region: FaceSwapRegion, point: CGPoint, width: Int, height: Int) -> Bool {
        if let mask = region.mask, mask.count == width * height {
            let x = min(width - 1, max(0, Int((point.x * CGFloat(width)).rounded(.down))))
            let y = min(height - 1, max(0, Int((point.y * CGFloat(height)).rounded(.down))))
            return mask[y * width + x] > 0
        }
        return FaceSwapOutlineValidation.contains(point, polygon: region.points)
    }

    private static func erode(_ mask: [UInt8], width: Int, height: Int, inset: Double) -> [UInt8] {
        let radius = Int((Double(min(width, height)) * min(0.12, max(0, inset))).rounded())
        guard radius > 0 else { return mask }
        var eroded = mask
        for y in 0..<height {
            for x in 0..<width {
                let index = y * width + x
                if mask[index] == 0 { continue }
                var nearEdge = false
                let minY = max(0, y - radius)
                let maxY = min(height - 1, y + radius)
                let minX = max(0, x - radius)
                let maxX = min(width - 1, x + radius)
                for sampleY in minY...maxY where !nearEdge {
                    for sampleX in minX...maxX where !nearEdge {
                        if mask[sampleY * width + sampleX] == 0 {
                            nearEdge = true
                        }
                    }
                }
                if nearEdge {
                    eroded[index] = 0
                }
            }
        }
        return eroded
    }
}
