import SwiftUI

/// Elevation sparkline with per-segment colors based on speed.
/// Shared visual language for the Live Activity and (optionally) in-app UI.
struct RideElevationProfileView: View {
    var points: [RideProfilePoint]
    var lineWidth: CGFloat = 2.5

    var body: some View {
        GeometryReader { geo in
            let size = geo.size
            if points.count >= 2, size.width > 1, size.height > 1 {
                let altitudes = points.map(\.relativeAltitude)
                let minAlt = altitudes.min() ?? 0
                let maxAlt = altitudes.max() ?? 0
                let span = max(maxAlt - minAlt, 1)
                let stepX = size.width / CGFloat(points.count - 1)

                ZStack {
                    // Soft baseline so a flat ride still reads as a chart.
                    Path { path in
                        let y = size.height * 0.7
                        path.move(to: CGPoint(x: 0, y: y))
                        path.addLine(to: CGPoint(x: size.width, y: y))
                    }
                    .stroke(Color.secondary.opacity(0.25), style: StrokeStyle(lineWidth: 1, dash: [3, 3]))

                    ForEach(0..<(points.count - 1), id: \.self) { index in
                        let a = points[index]
                        let b = points[index + 1]
                        Path { path in
                            path.move(to: point(for: a, at: index, stepX: stepX, height: size.height, minAlt: minAlt, span: span))
                            path.addLine(to: point(for: b, at: index + 1, stepX: stepX, height: size.height, minAlt: minAlt, span: span))
                        }
                        .stroke(color(for: a.displaySpeed), style: StrokeStyle(lineWidth: lineWidth, lineCap: .round, lineJoin: .round))
                    }
                }
            } else {
                // Placeholder while we wait for the first GPS/baro samples.
                RoundedRectangle(cornerRadius: 4)
                    .fill(Color.secondary.opacity(0.15))
                    .overlay(
                        Text("Ride profile")
                            .font(.caption2)
                            .foregroundStyle(.secondary)
                    )
            }
        }
    }

    private func point(
        for sample: RideProfilePoint,
        at index: Int,
        stepX: CGFloat,
        height: CGFloat,
        minAlt: Double,
        span: Double
    ) -> CGPoint {
        let x = CGFloat(index) * stepX
        let normalized = (sample.relativeAltitude - minAlt) / span
        // Invert Y so higher altitude draws toward the top; pad 10% vertically.
        let y = height * (0.9 - CGFloat(normalized) * 0.8)
        return CGPoint(x: x, y: y)
    }

    private func color(for speed: Double) -> Color {
        switch RideLiveFormatting.speedBucket(metersPerSecond: speed) {
        case 0: return Color.blue
        case 1: return Color.green
        case 2: return Color.orange
        default: return Color.red
        }
    }
}
