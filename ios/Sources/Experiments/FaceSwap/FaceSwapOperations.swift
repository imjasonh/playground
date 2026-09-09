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
    static let maximumChangedFraction = 0.45
    static let maximumFaceChangedFraction = 0.25

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
            if let box = rectangleRefusal(region) {
                return box
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
            if let box = rectangleRefusal(region) {
                return box
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
                outlines.append(region.outline(refersTo: region.id, role: .destination))
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
        let limit = commands.allSatisfy(isFaceEdit) ? maximumFaceChangedFraction : maximumChangedFraction
        guard fraction <= limit else {
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
        let width = image.width
        let height = image.height
        let count = width * height
        guard count > 0, mask.count == count else { return image }
        var source = [Int](repeating: -1, count: count)
        var distance = [Int](repeating: 0, count: count)
        var queue = [Int]()
        queue.reserveCapacity(count / 8)
        let neighbors = [(-1, 0), (1, 0), (0, -1), (0, 1)]
        for y in 0..<height {
            for x in 0..<width {
                let index = y * width + x
                if mask[index] == 0 { continue }
                var found = -1
                for (ox, oy) in neighbors {
                    let nx = x + ox
                    let ny = y + oy
                    guard nx >= 0, ny >= 0, nx < width, ny < height else { continue }
                    let neighbor = ny * width + nx
                    if mask[neighbor] == 0 {
                        found = neighbor
                        break
                    }
                }
                if found >= 0 {
                    source[index] = found
                    distance[index] = 1
                    queue.append(index)
                }
            }
        }
        var head = 0
        while head < queue.count {
            let index = queue[head]
            head += 1
            let x = index % width
            let y = index / width
            let nextDistance = distance[index] + 1
            for (ox, oy) in neighbors {
                let nx = x + ox
                let ny = y + oy
                guard nx >= 0, ny >= 0, nx < width, ny < height else { continue }
                let neighbor = ny * width + nx
                if mask[neighbor] == 0 || source[neighbor] >= 0 { continue }
                source[neighbor] = source[index]
                distance[neighbor] = nextDistance
                queue.append(neighbor)
            }
        }

        var filled = image.copy()
        for index in 0..<count {
            let from = source[index]
            guard from >= 0 else { continue }
            let offset = index * 4
            let sourceOffset = from * 4
            filled.rgba[offset] = image.rgba[sourceOffset]
            filled.rgba[offset + 1] = image.rgba[sourceOffset + 1]
            filled.rgba[offset + 2] = image.rgba[sourceOffset + 2]
        }
        for _ in 0..<4 {
            var next = filled
            for index in queue where distance[index] > 2 {
                let x = index % width
                let y = index / width
                var red = 0
                var green = 0
                var blue = 0
                var samples = 0
                for (ox, oy) in neighbors {
                    let nx = x + ox
                    let ny = y + oy
                    guard nx >= 0, ny >= 0, nx < width, ny < height else { continue }
                    let neighbor = ny * width + nx
                    let offset = neighbor * 4
                    red += Int(filled.rgba[offset])
                    green += Int(filled.rgba[offset + 1])
                    blue += Int(filled.rgba[offset + 2])
                    samples += 1
                }
                guard samples > 0 else { continue }
                let offset = index * 4
                next.rgba[offset] = UInt8(red / samples)
                next.rgba[offset + 1] = UInt8(green / samples)
                next.rgba[offset + 2] = UInt8(blue / samples)
            }
            filled = next
        }

        var output = image.copy()
        for index in 0..<count where mask[index] > 0 && source[index] >= 0 {
            let offset = index * 4
            output.rgba[offset] = filled.rgba[offset]
            output.rgba[offset + 1] = filled.rgba[offset + 1]
            output.rgba[offset + 2] = filled.rgba[offset + 2]
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
            for y in 0..<height {
                for x in 0..<width {
                    if sourceMask[y * width + x] == 0 { continue }
                    let destX = x + dx
                    let destY = y + dy
                    guard destX >= 0, destY >= 0, destX < width, destY < height else { continue }
                    guard let color = original.rgb(x: x, y: y) else { continue }
                    let weight = copyWeight(mask: sourceMask, x: x, y: y, width: width, height: height)
                    if let under = working.rgb(x: destX, y: destY), weight < 1 {
                        output.setRGB(
                            x: destX,
                            y: destY,
                            red: mix(color.0, under.0, weight),
                            green: mix(color.1, under.1, weight),
                            blue: mix(color.2, under.2, weight)
                        )
                    } else {
                        output.setRGB(x: destX, y: destY, red: color.0, green: color.1, blue: color.2)
                    }
                    writeMask[destY * width + destX] = 255
                    landed += 1
                }
            }
            if landed > 0 {
                outlines.append(
                    FaceSwapOutline(
                        id: "\(region.id)-copy-\(index + 1)",
                        role: .destination,
                        refersTo: region.id,
                        points: region.points
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

    private static func rectangleRefusal(_ region: FaceSwapRegion) -> String? {
        guard region.kind == .person, region.mask == nil else { return nil }
        return "\(region.id) is a rectangle, not a person outline. Nothing was changed."
    }

    private static func isFaceEdit(_ command: FaceSwapCommand) -> Bool {
        if case .replaceFaces = command { return true }
        return false
    }

    private static func copyWeight(mask: [UInt8], x: Int, y: Int, width: Int, height: Int) -> Double {
        let band = 3
        var nearest = band
        let minY = max(0, y - band)
        let maxY = min(height - 1, y + band)
        let minX = max(0, x - band)
        let maxX = min(width - 1, x + band)
        for sampleY in minY...maxY {
            for sampleX in minX...maxX where mask[sampleY * width + sampleX] == 0 {
                nearest = min(nearest, max(abs(sampleX - x), abs(sampleY - y)))
            }
        }
        return min(1, Double(nearest) / Double(band))
    }

    private static func mix(_ edited: UInt8, _ original: UInt8, _ weight: Double) -> UInt8 {
        let value = Double(edited) * weight + Double(original) * (1 - weight)
        return UInt8(min(255, max(0, value.rounded())))
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
