import CoreGraphics
import Foundation

/// Closes a jaw landmark into a face-skin contour and formats it for the model.
///
/// The on-device model on iOS 26 cannot see the photo. It chooses among these
/// contours. It does not receive a bounding box, and it cannot invent a new one.
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

    static func catalog(_ candidates: [FaceSwapCandidate]) -> String {
        var lines = [
            "Face contours already traced. Normalized, origin top-left, x and y from 0 to 1.",
            "Choose sourceId and destinationId from these ids only. Do not invent points or a box."
        ]
        for candidate in candidates.prefix(6) {
            let points = candidate.points.prefix(16).map { point in
                String(format: "%.2f,%.2f", point.x, point.y)
            }.joined(separator: " ")
            lines.append(
                String(
                    format: "id=%@ place=%@ chinContrast=%.2f points=%@",
                    candidate.id,
                    candidate.place,
                    candidate.chinContrast,
                    points
                )
            )
        }
        return AgentContextBudget.truncateToChars(lines.joined(separator: "\n"), maxChars: 900)
    }

    static func assign(
        sourceId: String,
        destinationId: String,
        sourcePhrase: String,
        destinationPhrase: String,
        candidates: [FaceSwapCandidate]
    ) -> Result<(source: FaceSwapOutline, destination: FaceSwapOutline), String> {
        let sourceKey = normalize(sourceId)
        let destinationKey = normalize(destinationId)
        guard sourceKey != destinationKey else {
            return .failure("Source and destination must be different face contours.")
        }
        guard let source = candidates.first(where: { normalize($0.id) == sourceKey }) else {
            return .failure("Unknown source contour \(sourceId).")
        }
        guard let destination = candidates.first(where: { normalize($0.id) == destinationKey }) else {
            return .failure("Unknown destination contour \(destinationId).")
        }
        let pair = (
            source: FaceSwapOutline(
                id: source.id,
                role: .source,
                refersTo: phrase(sourcePhrase, fallback: "source face"),
                points: source.points
            ),
            destination: FaceSwapOutline(
                id: destination.id,
                role: .destination,
                refersTo: phrase(destinationPhrase, fallback: "destination face"),
                points: destination.points
            )
        )
        return FaceSwapOutlineValidation.prepare([pair.source, pair.destination])
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

    private static func normalize(_ id: String) -> String {
        id.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
    }

    private static func phrase(_ raw: String, fallback: String) -> String {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        return trimmed.isEmpty ? fallback : String(trimmed.prefix(40))
    }
}
