import CoreGraphics
import Foundation

/// Closed face outline in normalized image space, origin top-left.
struct FaceSwapOutline: Equatable, Identifiable, Sendable {
    enum Role: String, Equatable, Sendable {
        case source
        case destination
    }

    var id: String
    var role: Role
    var refersTo: String
    var points: [CGPoint]

    var displayLine: String {
        let phrase = refersTo.isEmpty ? role.rawValue : refersTo
        return "\(phrase), \(role.rawValue), \(points.count) points"
    }
}

/// How the model wants the destination face reconstructed. Coordinates stay locked.
///
/// This is a recipe, not a bitmap. The compositor keeps destination shading,
/// transfers source identity under that light, and cannot grow the outline.
struct FaceSwapEditPlan: Equatable, Sendable {
    /// 0 keeps source proportions. 1 reshapes them onto the destination pose.
    var fitPose: Double
    /// How far to place source color under destination light. Clamped to at least 0.35 so the edit is not a raw copy.
    var lightingMatch: Double
    /// 0 keeps source color. 1 pulls the reconstruction toward destination color.
    var colorMatch: Double
    /// 0 drops source micro-contrast. 1 adds it after relighting, without copying the crop.
    var detailTransfer: Double
    /// Inward seam width as a fraction of the shorter outline side. Cannot grow the outline.
    var edgeBand: Double
    /// Shrinks the write region toward the outline center. Cannot enlarge it.
    var inset: Double
    /// Why this recipe fits the request. Shown in the tool log. Does not move pixels.
    var motive: String
    /// Optional tighter destination skin contour in normalized space. Empty keeps the traced outline.
    var tightenedDestination: [CGPoint]

    static let identity = FaceSwapEditPlan(
        fitPose: 0.8,
        lightingMatch: 0.75,
        colorMatch: 0.4,
        detailTransfer: 0.35,
        edgeBand: 0.08,
        inset: 0.02,
        motive: "",
        tightenedDestination: []
    )

    func clamped() -> FaceSwapEditPlan {
        FaceSwapEditPlan(
            fitPose: Self.unit(fitPose),
            lightingMatch: min(1, max(0.35, lightingMatch)),
            colorMatch: Self.unit(colorMatch),
            detailTransfer: Self.unit(detailTransfer),
            edgeBand: min(0.16, max(0.02, edgeBand)),
            inset: min(0.12, max(0, inset)),
            motive: String(motive.trimmingCharacters(in: .whitespacesAndNewlines).prefix(120)),
            tightenedDestination: Array(tightenedDestination.prefix(FaceSwapOutlineValidation.maximumPoints))
        )
    }

    private static func unit(_ value: Double) -> Double {
        min(1, max(0, value))
    }
}

enum FaceSwapOutlineValidation {
    static let minimumPoints = 6
    static let maximumPoints = 24
    static let minimumArea = 0.004
    static let maximumArea = 0.18

    static func prepare(_ outlines: [FaceSwapOutline]) -> Result<(source: FaceSwapOutline, destination: FaceSwapOutline), String> {
        let limited = Array(outlines.prefix(2))
        guard limited.count == 2 else {
            return .failure("Need a source outline and a destination outline. Got \(outlines.count).")
        }
        var source: FaceSwapOutline?
        var destination: FaceSwapOutline?
        for outline in limited {
            switch outline.role {
            case .source:
                source = sanitize(outline)
            case .destination:
                destination = sanitize(outline)
            }
        }
        guard let source, let destination else {
            return .failure("Each outline needs role source or destination.")
        }
        if let error = check(source) { return .failure(error) }
        if let error = check(destination) { return .failure(error) }
        return .success((source, destination))
    }

    static func check(_ outline: FaceSwapOutline) -> String? {
        guard outline.points.count >= minimumPoints else {
            return "\(outline.refersTo) outline needs at least \(minimumPoints) points."
        }
        guard outline.points.count <= maximumPoints else {
            return "\(outline.refersTo) outline has too many points."
        }
        for point in outline.points {
            if point.x < 0 || point.x > 1 || point.y < 0 || point.y > 1 {
                return "\(outline.refersTo) outline point is outside the photo."
            }
        }
        let area = abs(shoelace(outline.points))
        if area < minimumArea {
            return "\(outline.refersTo) outline is too small to edit."
        }
        if area > maximumArea {
            return "\(outline.refersTo) outline covers too much of the photo. Trace only the face."
        }
        let bounds = boundsOf(outline.points)
        if bounds.width > 0.55 || bounds.height > 0.55 {
            return "\(outline.refersTo) outline is too wide to be one face. Trace only the face."
        }
        if isBox(outline.points, bounds: bounds) {
            return "\(outline.refersTo) outline is a box, not a face contour. Trace the skin edge."
        }
        return nil
    }

    /// A tighter contour is usable only when every point stays inside the traced face.
    static func acceptedTightening(base: [CGPoint], tightened: [CGPoint]) -> [CGPoint]? {
        guard tightened.count >= minimumPoints, tightened.count <= maximumPoints else { return nil }
        for point in tightened {
            if point.x < 0 || point.x > 1 || point.y < 0 || point.y > 1 { return nil }
            if !contains(point, polygon: base) && !nearEdge(point, polygon: base) { return nil }
        }
        let tightenedArea = abs(shoelace(tightened))
        let baseArea = abs(shoelace(base))
        if tightenedArea < minimumArea || tightenedArea > baseArea + 0.0001 { return nil }
        return tightened
    }

    static func boundsOf(_ points: [CGPoint]) -> CGRect {
        guard let first = points.first else { return .zero }
        var minX = first.x
        var maxX = first.x
        var minY = first.y
        var maxY = first.y
        for point in points.dropFirst() {
            minX = min(minX, point.x)
            maxX = max(maxX, point.x)
            minY = min(minY, point.y)
            maxY = max(maxY, point.y)
        }
        return CGRect(x: minX, y: minY, width: maxX - minX, height: maxY - minY)
    }

    static func pixelPoints(_ outline: FaceSwapOutline, width: Int, height: Int, inset: Double) -> [CGPoint] {
        let points = insetPoints(outline.points, fraction: inset)
        return points.map { point in
            CGPoint(
                x: min(CGFloat(width - 1), max(0, point.x * CGFloat(width))),
                y: min(CGFloat(height - 1), max(0, point.y * CGFloat(height)))
            )
        }
    }

    static func contains(_ point: CGPoint, polygon: [CGPoint]) -> Bool {
        guard polygon.count >= 3 else { return false }
        var inside = false
        var previous = polygon[polygon.count - 1]
        for current in polygon {
            let crosses = (current.y > point.y) != (previous.y > point.y)
            if crosses {
                let xIntersect = (previous.x - current.x) * (point.y - current.y) / (previous.y - current.y) + current.x
                if point.x < xIntersect {
                    inside.toggle()
                }
            }
            previous = current
        }
        return inside
    }

    static func mask(polygon: [CGPoint], width: Int, height: Int) -> [UInt8] {
        var mask = [UInt8](repeating: 0, count: max(0, width * height))
        guard width > 0, height > 0, polygon.count >= 3 else { return mask }
        let bounds = boundsOf(polygon)
        let minX = max(0, Int(bounds.minX.rounded(.down)))
        let maxX = min(width - 1, Int(bounds.maxX.rounded(.up)))
        let minY = max(0, Int(bounds.minY.rounded(.down)))
        let maxY = min(height - 1, Int(bounds.maxY.rounded(.up)))
        guard minX <= maxX, minY <= maxY else { return mask }
        for y in minY...maxY {
            for x in minX...maxX {
                let sample = CGPoint(x: Double(x) + 0.5, y: Double(y) + 0.5)
                if contains(sample, polygon: polygon) {
                    mask[y * width + x] = 255
                }
            }
        }
        return mask
    }

    static func promptBlock(_ outlines: [FaceSwapOutline]) -> String {
        var lines = ["Face outlines, normalized, origin top-left, x and y from 0 to 1."]
        for outline in outlines.prefix(2) {
            let points = outline.points.prefix(maximumPoints).map { point in
                String(format: "%.2f,%.2f", point.x, point.y)
            }.joined(separator: " ")
            let phrase = outline.refersTo.isEmpty ? outline.role.rawValue : outline.refersTo
            lines.append("\(outline.role.rawValue) id=\(outline.id) refersTo=\(phrase) points=\(points)")
        }
        lines.append("applyRegionEdit reconstructs inside the destination outline. It cannot enlarge it.")
        lines.append("tightenedDestination may shrink the skin contour. Points outside the destination outline are ignored.")
        return AgentContextBudget.truncateToChars(lines.joined(separator: "\n"), maxChars: 900)
    }

    private static func isBox(_ points: [CGPoint], bounds: CGRect) -> Bool {
        guard bounds.width > 0, bounds.height > 0 else { return false }
        let tolerance: CGFloat = 0.012
        return points.allSatisfy { point in
            let onVertical = abs(point.x - bounds.minX) <= tolerance || abs(point.x - bounds.maxX) <= tolerance
            let onHorizontal = abs(point.y - bounds.minY) <= tolerance || abs(point.y - bounds.maxY) <= tolerance
            return onVertical || onHorizontal
        }
    }

    private static func nearEdge(_ point: CGPoint, polygon: [CGPoint]) -> Bool {
        guard polygon.count >= 2 else { return false }
        let tolerance: CGFloat = 0.015
        for index in polygon.indices {
            let start = polygon[index]
            let end = polygon[(index + 1) % polygon.count]
            let dx = end.x - start.x
            let dy = end.y - start.y
            let lengthSquared = dx * dx + dy * dy
            let t: CGFloat
            if lengthSquared < 0.000_000_1 {
                t = 0
            } else {
                t = min(1, max(0, ((point.x - start.x) * dx + (point.y - start.y) * dy) / lengthSquared))
            }
            let closestX = start.x + t * dx
            let closestY = start.y + t * dy
            let distance = hypot(point.x - closestX, point.y - closestY)
            if distance <= tolerance { return true }
        }
        return false
    }

    private static func sanitize(_ outline: FaceSwapOutline) -> FaceSwapOutline {
        var copy = outline
        copy.points = Array(outline.points.prefix(maximumPoints))
        copy.refersTo = outline.refersTo.trimmingCharacters(in: .whitespacesAndNewlines)
        return copy
    }

    private static func insetPoints(_ points: [CGPoint], fraction: Double) -> [CGPoint] {
        guard fraction > 0, let first = points.first else { return points }
        var centroid = first
        for point in points.dropFirst() {
            centroid.x += point.x
            centroid.y += point.y
        }
        let count = CGFloat(points.count)
        centroid.x /= count
        centroid.y /= count
        let keep = CGFloat(1 - min(0.12, max(0, fraction)))
        return points.map { point in
            CGPoint(
                x: centroid.x + (point.x - centroid.x) * keep,
                y: centroid.y + (point.y - centroid.y) * keep
            )
        }
    }

    private static func shoelace(_ points: [CGPoint]) -> CGFloat {
        guard points.count >= 3 else { return 0 }
        var sum: CGFloat = 0
        for index in points.indices {
            let next = points[(index + 1) % points.count]
            sum += points[index].x * next.y - next.x * points[index].y
        }
        return sum / 2
    }
}

enum FaceSwapRoleParser {
    static func role(from raw: String) -> FaceSwapOutline.Role? {
        let text = raw.lowercased()
        if text.contains("dest") || text.contains("target") || text.contains("onto") {
            return .destination
        }
        if text.contains("source") || text.contains("from") {
            return .source
        }
        return nil
    }
}
