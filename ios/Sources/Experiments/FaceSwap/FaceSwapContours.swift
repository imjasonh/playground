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
        let arc = (1...3).map { step -> CGPoint in
            let t = CGFloat(step) / 4
            let u = 1 - t
            return CGPoint(
                x: min(1, max(0, u * u * last.x + 2 * u * t * crown.x + t * t * first.x)),
                y: min(1, max(0, u * u * last.y + 2 * u * t * crown.y + t * t * first.y))
            )
        }
        return jaw + arc
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
