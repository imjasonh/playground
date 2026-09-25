import CoreGraphics
import Foundation

/// Camera motion between two frames as a uniform scale plus a shift: a point
/// `p` moves to `scale * p + (dx, dy)`.
///
/// A phone filming a flat sign mostly pans and zooms, which this models. The
/// units are whatever the points use, normalized or pixels.
struct LiveTranslateMotion: Equatable {
    var scale: CGFloat = 1
    var dx: CGFloat = 0
    var dy: CGFloat = 0

    static let identity = LiveTranslateMotion()

    func apply(to point: CGPoint) -> CGPoint {
        CGPoint(x: point.x * scale + dx, y: point.y * scale + dy)
    }

    /// Moves the box's center and scales its size about that center.
    func apply(to box: CGRect) -> CGRect {
        let center = apply(to: CGPoint(x: box.midX, y: box.midY))
        let width = box.width * scale
        let height = box.height * scale
        return CGRect(x: center.x - width / 2, y: center.y - height / 2, width: width, height: height)
    }

    /// This motion followed by `next`.
    func then(_ next: LiveTranslateMotion) -> LiveTranslateMotion {
        LiveTranslateMotion(
            scale: scale * next.scale,
            dx: dx * next.scale + next.dx,
            dy: dy * next.scale + next.dy
        )
    }

    /// Fits matched points while ignoring outliers.
    ///
    /// The scale is the median ratio of distances between pairs of points,
    /// skipping pairs closer than `minimumSpan` and clamping to `scaleRange`.
    /// The shift is the median of what's left after scaling. One point gives a
    /// pure shift, and none gives the identity.
    static func fit(
        _ pairs: [(from: CGPoint, to: CGPoint)],
        minimumSpan: CGFloat,
        scaleRange: ClosedRange<CGFloat>
    ) -> LiveTranslateMotion {
        guard !pairs.isEmpty else { return .identity }
        var ratios: [CGFloat] = []
        for first in pairs.indices {
            for second in pairs.indices where second > first {
                let before = distance(pairs[first].from, pairs[second].from)
                guard before >= minimumSpan else { continue }
                ratios.append(distance(pairs[first].to, pairs[second].to) / before)
            }
        }
        let scale = ratios.isEmpty
            ? 1
            : min(max(median(ratios), scaleRange.lowerBound), scaleRange.upperBound)
        return LiveTranslateMotion(
            scale: scale,
            dx: median(pairs.map { $0.to.x - scale * $0.from.x }),
            dy: median(pairs.map { $0.to.y - scale * $0.from.y })
        )
    }

    static func median(_ values: [CGFloat]) -> CGFloat {
        let sorted = values.sorted()
        let middle = sorted.count / 2
        return sorted.count % 2 == 0 ? (sorted[middle - 1] + sorted[middle]) / 2 : sorted[middle]
    }

    private static func distance(_ lhs: CGPoint, _ rhs: CGPoint) -> CGFloat {
        hypot(lhs.x - rhs.x, lhs.y - rhs.y)
    }
}
