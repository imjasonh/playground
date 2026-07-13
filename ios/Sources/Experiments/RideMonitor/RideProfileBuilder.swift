import Foundation

/// Builds a small elevation/speed sparkline from the live barometer + GPS
/// buffers. ActivityKit content has a tight size budget, so we cap the point
/// count and pick evenly spaced samples.
enum RideProfileBuilder {
    /// Default point budget for Live Activity / Watch payloads.
    static let defaultMaxPoints = 48

    static func build(
        altitudes: [AltitudeSample],
        track: [LocationSample],
        maxPoints: Int = defaultMaxPoints
    ) -> [RideProfilePoint] {
        guard maxPoints > 0 else { return [] }

        let source: [RideProfilePoint]
        if !altitudes.isEmpty {
            source = altitudes.map { sample in
                RideProfilePoint(
                    relativeAltitude: sample.relativeAltitude,
                    speedMetersPerSecond: nearestSpeed(at: sample.t, in: track)
                )
            }
        } else if !track.isEmpty {
            // Fall back to GPS altitude when the barometer isn't available.
            let baseline = track.first?.altitude ?? 0
            source = track.map { sample in
                RideProfilePoint(
                    relativeAltitude: sample.altitude - baseline,
                    speedMetersPerSecond: sample.speed
                )
            }
        } else {
            return []
        }

        return RideLiveFormatting.downsample(source, maxPoints: maxPoints)
    }

    static func nearestSpeed(at t: TimeInterval, in track: [LocationSample]) -> Double {
        guard let nearest = track.min(by: { abs($0.t - t) < abs($1.t - t) }) else {
            return -1
        }
        return nearest.speed
    }
}
