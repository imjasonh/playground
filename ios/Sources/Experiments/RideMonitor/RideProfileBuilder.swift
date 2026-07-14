import Foundation

/// Builds an elevation/speed sparkline from barometer + GPS samples.
/// Used by the Live Activity (tight ActivityKit budget) and the past-ride
/// detail view (larger in-app point budget).
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
