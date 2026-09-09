import CoreGraphics
import Foundation

enum FaceSwapCommand: Equatable, Sendable {
    case remove(regionID: String, inset: Double)
    case copy(sourceID: String, centers: [CGPoint])
    case replaceFaces(sourceID: String, destinationIDs: [String], plan: FaceSwapEditPlan)
}

struct FaceSwapScriptResult: Equatable, Sendable {
    var image: FaceSwapRaster
    var writeMask: [UInt8]
    var outlines: [FaceSwapOutline]
    var log: [String]
    var stats: FaceSwapEditStats
}

/// Applies model tool calls. Each call writes only inside a catalog region.
enum FaceSwapOperations {
    static let maximumCopies = 6
    static let maximumFaces = 8
    static let maximumChangedFraction = 0.75

    static func validate(_ command: FaceSwapCommand, regions: [FaceSwapRegion], width: Int, height: Int) -> String? {
        switch command {
        case .remove(let regionID, _):
            guard let region = FaceSwapRegions.region(id: regionID, in: regions) else {
                return "Unknown region \(regionID)."
            }
            let mask = FaceSwapRegions.writeMask(region, width: width, height: height, inset: 0)
            if FaceSwapRegions.fraction(mask) > FaceSwapRegions.maximumRegionFraction {
                return "\(region.id) covers too much of the photo to erase as one region."
            }
            if FaceSwapRegions.fraction(mask) == 0 {
                return "\(region.id) has an empty write region."
            }
            return nil
        case .copy(let sourceID, let centers):
            guard let region = FaceSwapRegions.region(id: sourceID, in: regions) else {
                return "Unknown region \(sourceID)."
            }
            guard !centers.isEmpty, centers.count <= maximumCopies else {
                return "copyRegion needs 1 to \(maximumCopies) new centers. The original stays."
            }
            for center in centers {
                if center.x < 0 || center.x > 1 || center.y < 0 || center.y > 1 {
                    return "A copy center is outside the photo."
                }
            }
            let mask = FaceSwapRegions.writeMask(region, width: width, height: height, inset: 0)
            if FaceSwapRegions.fraction(mask) > FaceSwapRegions.maximumRegionFraction {
                return "\(region.id) is too large to copy."
            }
            return nil
        case .replaceFaces(let sourceID, let destinationIDs, _):
            guard let source = FaceSwapRegions.region(id: sourceID, in: regions), source.kind == .face else {
                return "replaceFaces source must be a face id."
            }
            let destinations = destinationIDs.prefix(maximumFaces)
            guard !destinations.isEmpty else {
                return "replaceFaces needs at least one destination face id."
            }
            for destinationID in destinations {
                guard let destination = FaceSwapRegions.region(id: destinationID, in: regions), destination.kind == .face else {
                    return "Unknown face \(destinationID)."
                }
                if destination.id.lowercased() == source.id.lowercased() {
                    return "Do not replace a face with itself."
                }
            }
            return nil
        }
    }

    static func apply(
        commands: [FaceSwapCommand],
        regions: [FaceSwapRegion],
        original: FaceSwapRaster
    ) -> Result<FaceSwapScriptResult, FaceSwapMessageError> {
        guard !commands.isEmpty else {
            return .failure("The model did not choose an edit. No pixels changed.")
        }
        var working = original
        var union = [UInt8](repeating: 0, count: original.pixelCount)
        var outlines: [FaceSwapOutline] = []
        var log: [String] = []
        for command in commands {
            if let error = validate(command, regions: regions, width: original.width, height: original.height) {
                return .failure(FaceSwapMessageError(error))
            }
            switch command {
            case .remove(let regionID, let inset):
                guard let region = FaceSwapRegions.region(id: regionID, in: regions) else {
                    return .failure("Unknown region \(regionID).")
                }
                let mask = FaceSwapRegions.writeMask(region, width: original.width, height: original.height, inset: inset)
                working = fillFromOutside(working, mask: mask)
                merge(mask, into: &union)
                outlines.append(region.outline(refersTo: "remove \(region.id)", role: .destination))
                log.append("removeRegion \(region.id)")
            case .copy(let sourceID, let centers):
                guard let region = FaceSwapRegions.region(id: sourceID, in: regions) else {
                    return .failure("Unknown region \(sourceID).")
                }
                let copied = copyRegion(region, from: original, onto: working, centers: centers)
                working = copied.image
                merge(copied.writeMask, into: &union)
                outlines.append(contentsOf: copied.outlines)
                log.append("copyRegion \(region.id) copies=\(centers.count)")
            case .replaceFaces(let sourceID, let destinationIDs, let plan):
                guard let source = FaceSwapRegions.region(id: sourceID, in: regions) else {
                    return .failure("Unknown region \(sourceID).")
                }
                let replaced = replaceFaces(
                    source: source,
                    destinationIDs: destinationIDs,
                    plan: plan,
                    regions: regions,
                    original: original,
                    working: working
                )
                switch replaced {
                case .success(let output):
                    working = output.image
                    merge(output.writeMask, into: &union)
                    outlines.append(contentsOf: output.outlines)
                    log.append("replaceFaces \(source.id) onto \(destinationIDs.joined(separator: ","))")
                case .failure(let message):
                    return .failure(message)
                }
            }
        }
        let outside = pixelsChangedOutside(before: original, after: working, mask: union)
        guard outside == 0 else {
            return .failure("The edit changed pixels outside the chosen regions. Nothing was kept.")
        }
        let changed = FaceSwapDiff.changedPixelCount(original: original, edited: working)
        let fraction = Double(changed) / Double(max(original.pixelCount, 1))
        guard fraction <= maximumChangedFraction else {
            return .failure("The edit changed too much of the photo. Nothing was kept.")
        }
        guard changed > 0 else {
            return .failure("The edit wrote 0 pixels. Nothing was kept.")
        }
        let stats = FaceSwapEditStats(
            sourceID: log.first ?? "tools",
            destinationID: log.joined(separator: "; "),
            writtenPixels: union.reduce(0) { $0 + ($1 > 0 ? 1 : 0) },
            changedFromOriginal: changed,
            totalPixels: original.pixelCount,
            outsideMaskChanged: outside,
            warp: "tools"
        )
        return .success(
            FaceSwapScriptResult(image: working, writeMask: union, outlines: outlines, log: log, stats: stats)
        )
    }

    static func fillFromOutside(_ image: FaceSwapRaster, mask: [UInt8]) -> FaceSwapRaster {
        var output = image.copy()
        let width = image.width
        let height = image.height
        for y in 0..<height {
            for x in 0..<width {
                if mask[y * width + x] == 0 { continue }
                guard let color = nearestOutsideColor(image, mask: mask, x: x, y: y) else { continue }
                output.setRGB(x: x, y: y, red: color.0, green: color.1, blue: color.2)
            }
        }
        return output
    }

    private static func copyRegion(
        _ region: FaceSwapRegion,
        from original: FaceSwapRaster,
        onto working: FaceSwapRaster,
        centers: [CGPoint]
    ) -> (image: FaceSwapRaster, writeMask: [UInt8], outlines: [FaceSwapOutline]) {
        let width = original.width
        let height = original.height
        let sourceMask = FaceSwapRegions.writeMask(region, width: width, height: height, inset: 0)
        let centroid = centroid(of: sourceMask, width: width, height: height)
        var output = working.copy()
        var writeMask = [UInt8](repeating: 0, count: original.pixelCount)
        var outlines: [FaceSwapOutline] = []
        for (index, center) in centers.enumerated() {
            let dx = Int((center.x * CGFloat(width)).rounded()) - Int(centroid.x.rounded())
            let dy = Int((center.y * CGFloat(height)).rounded()) - Int(centroid.y.rounded())
            var landed = 0
            var minX = width
            var minY = height
            var maxX = 0
            var maxY = 0
            for y in 0..<height {
                for x in 0..<width {
                    if sourceMask[y * width + x] == 0 { continue }
                    let destX = x + dx
                    let destY = y + dy
                    guard destX >= 0, destY >= 0, destX < width, destY < height else { continue }
                    guard let color = original.rgb(x: x, y: y) else { continue }
                    output.setRGB(x: destX, y: destY, red: color.0, green: color.1, blue: color.2)
                    writeMask[destY * width + destX] = 255
                    landed += 1
                    minX = min(minX, destX)
                    minY = min(minY, destY)
                    maxX = max(maxX, destX)
                    maxY = max(maxY, destY)
                }
            }
            if landed > 0 {
                outlines.append(
                    FaceSwapOutline(
                        id: "\(region.id)-copy-\(index + 1)",
                        role: .destination,
                        refersTo: "copy of \(region.id)",
                        points: boxPoints(
                            minX: minX,
                            minY: minY,
                            maxX: maxX,
                            maxY: maxY,
                            width: width,
                            height: height
                        )
                    )
                )
            }
        }
        return (output, writeMask, outlines)
    }

    private static func replaceFaces(
        source: FaceSwapRegion,
        destinationIDs: [String],
        plan: FaceSwapEditPlan,
        regions: [FaceSwapRegion],
        original: FaceSwapRaster,
        working: FaceSwapRaster
    ) -> Result<(image: FaceSwapRaster, writeMask: [UInt8], outlines: [FaceSwapOutline]), FaceSwapMessageError> {
        var current = working
        var writeMask = [UInt8](repeating: 0, count: original.pixelCount)
        var outlines: [FaceSwapOutline] = [
            source.outline(refersTo: source.id, role: .source),
        ]
        let landmarks = FaceSwapLandmarks.locate(raster: original)
        let sourceOutline = source.outline(refersTo: source.id, role: .source)
        for destinationID in destinationIDs.prefix(maximumFaces) {
            guard let destination = FaceSwapRegions.region(id: destinationID, in: regions) else {
                return .failure("Unknown face \(destinationID).")
            }
            let destinationOutline = destination.outline(refersTo: destination.id, role: .destination)
            let output = FaceSwapEditor.apply(
                plan: plan,
                source: sourceOutline,
                destination: destinationOutline,
                original: original,
                working: current,
                sourceLandmarks: FaceSwapLandmarks.trio(
                    inside: sourceOutline,
                    candidates: landmarks,
                    width: original.width,
                    height: original.height
                ),
                destinationLandmarks: FaceSwapLandmarks.trio(
                    inside: destinationOutline,
                    candidates: landmarks,
                    width: original.width,
                    height: original.height
                )
            )
            switch output {
            case .success(let paste):
                guard paste.stats.outsideMaskChanged == 0 else {
                    return .failure("replaceFaces changed pixels outside \(destination.id).")
                }
                current = paste.image
                merge(paste.mask, into: &writeMask)
                outlines.append(destinationOutline)
            case .failure(let message):
                return .failure(message)
            }
        }
        return .success((current, writeMask, outlines))
    }

    private static func nearestOutsideColor(
        _ image: FaceSwapRaster,
        mask: [UInt8],
        x: Int,
        y: Int
    ) -> (UInt8, UInt8, UInt8)? {
        let width = image.width
        let height = image.height
        var red = 0
        var green = 0
        var blue = 0
        var count = 0
        for radius in 1...48 {
            let minY = max(0, y - radius)
            let maxY = min(height - 1, y + radius)
            let minX = max(0, x - radius)
            let maxX = min(width - 1, x + radius)
            if minY == y - radius {
                for sampleX in minX...maxX {
                    accumulate(image, mask: mask, x: sampleX, y: minY, red: &red, green: &green, blue: &blue, count: &count)
                }
            }
            if maxY != minY, maxY == y + radius {
                for sampleX in minX...maxX {
                    accumulate(image, mask: mask, x: sampleX, y: maxY, red: &red, green: &green, blue: &blue, count: &count)
                }
            }
            if minX == x - radius {
                for sampleY in (minY + 1)..<maxY {
                    accumulate(image, mask: mask, x: minX, y: sampleY, red: &red, green: &green, blue: &blue, count: &count)
                }
            }
            if maxX != minX, maxX == x + radius {
                for sampleY in (minY + 1)..<maxY {
                    accumulate(image, mask: mask, x: maxX, y: sampleY, red: &red, green: &green, blue: &blue, count: &count)
                }
            }
            if count > 0 {
                return (
                    UInt8(red / count),
                    UInt8(green / count),
                    UInt8(blue / count)
                )
            }
        }
        return nil
    }

    private static func accumulate(
        _ image: FaceSwapRaster,
        mask: [UInt8],
        x: Int,
        y: Int,
        red: inout Int,
        green: inout Int,
        blue: inout Int,
        count: inout Int
    ) {
        let index = y * image.width + x
        if mask[index] > 0 { return }
        guard let color = image.rgb(x: x, y: y) else { return }
        red += Int(color.0)
        green += Int(color.1)
        blue += Int(color.2)
        count += 1
    }

    private static func centroid(of mask: [UInt8], width: Int, height: Int) -> CGPoint {
        var sumX = 0.0
        var sumY = 0.0
        var count = 0.0
        for y in 0..<height {
            for x in 0..<width {
                if mask[y * width + x] == 0 { continue }
                sumX += Double(x) + 0.5
                sumY += Double(y) + 0.5
                count += 1
            }
        }
        guard count > 0 else { return CGPoint(x: CGFloat(width) / 2, y: CGFloat(height) / 2) }
        return CGPoint(x: sumX / count, y: sumY / count)
    }

    private static func boxPoints(minX: Int, minY: Int, maxX: Int, maxY: Int, width: Int, height: Int) -> [CGPoint] {
        let left = min(1, max(0, CGFloat(minX) / CGFloat(max(width, 1))))
        let top = min(1, max(0, CGFloat(minY) / CGFloat(max(height, 1))))
        let right = min(1, max(0, CGFloat(maxX + 1) / CGFloat(max(width, 1))))
        let bottom = min(1, max(0, CGFloat(maxY + 1) / CGFloat(max(height, 1))))
        return [
            CGPoint(x: left, y: top),
            CGPoint(x: (left + right) / 2, y: top),
            CGPoint(x: right, y: top),
            CGPoint(x: right, y: (top + bottom) / 2),
            CGPoint(x: right, y: bottom),
            CGPoint(x: (left + right) / 2, y: bottom),
            CGPoint(x: left, y: bottom),
            CGPoint(x: left, y: (top + bottom) / 2),
        ]
    }

    private static func merge(_ mask: [UInt8], into union: inout [UInt8]) {
        guard mask.count == union.count else { return }
        for index in union.indices where mask[index] > 0 {
            union[index] = 255
        }
    }

    private static func pixelsChangedOutside(before: FaceSwapRaster, after: FaceSwapRaster, mask: [UInt8]) -> Int {
        var count = 0
        for pixel in 0..<before.pixelCount {
            if pixel < mask.count, mask[pixel] > 0 { continue }
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
