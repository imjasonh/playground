import CoreGraphics
import Foundation

/// Closes a jaw landmark into a face-skin contour.
enum FaceSwapContours {
    static func closeJaw(_ jaw: [CGPoint], brows: [CGPoint]) -> [CGPoint] {
        guard jaw.count >= 4, let first = jaw.first, let last = jaw.last else { return jaw }
        let bounds = FaceSwapOutlineValidation.boundsOf(jaw)
        let browCenter = average(brows) ?? CGPoint(x: (first.x + last.x) / 2, y: bounds.minY)
        var crown = browCenter
        crown.y = min(crown.y, bounds.minY) - max(0.02, bounds.height * 0.35)
        crown.x = min(1, max(0, crown.x))
        crown.y = min(1, max(0, crown.y))
        // The crown is only a Bezier control point, so sampled arc points never reach it.
        // Insert it so the closed contour actually covers the forehead above the brows.
        let left = curve(0.25, from: last, to: first, control: crown)
        let right = curve(0.75, from: last, to: first, control: crown)
        return jaw + [left, crown, right]
    }

    private static func curve(_ t: CGFloat, from start: CGPoint, to end: CGPoint, control: CGPoint) -> CGPoint {
        let u = 1 - t
        return CGPoint(
            x: min(1, max(0, u * u * start.x + 2 * u * t * control.x + t * t * end.x)),
            y: min(1, max(0, u * u * start.y + 2 * u * t * control.y + t * t * end.y))
        )
    }

    static func decimate(_ points: [CGPoint], limit: Int) -> [CGPoint] {
        guard limit >= 3, points.count > limit else { return points }
        let lastIndex = points.count - 1
        return (0..<limit).map { step in
            let index = Int((Double(step) * Double(lastIndex) / Double(limit - 1)).rounded())
            return points[min(lastIndex, max(0, index))]
        }
    }

    static func place(for center: CGPoint) -> String {
        let horizontal: String
        if center.x < 0.38 {
            horizontal = "left"
        } else if center.x > 0.62 {
            horizontal = "right"
        } else {
            horizontal = "center"
        }
        let vertical: String
        if center.y < 0.38 {
            vertical = "higher"
        } else if center.y > 0.62 {
            vertical = "lower"
        } else {
            vertical = "middle"
        }
        return "\(horizontal), \(vertical)"
    }

    private static func average(_ points: [CGPoint]) -> CGPoint? {
        guard let first = points.first else { return nil }
        var sum = first
        for point in points.dropFirst() {
            sum.x += point.x
            sum.y += point.y
        }
        let count = CGFloat(points.count)
        return CGPoint(x: sum.x / count, y: sum.y / count)
    }
}
