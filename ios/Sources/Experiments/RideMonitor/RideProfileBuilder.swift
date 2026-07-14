import Foundation

/// Builds an elevation/speed sparkline from barometer + GPS samples.
/// Used by the Live Activity (tight ActivityKit budget) and the past-ride
/// detail view (larger in-app point budget).
///
/// ## Complexity
///
/// Live snapshots are rebuilt about once a second while riding. Older builds
/// mapped **every** barometer sample through a linear nearest-speed scan of
/// the GPS track before downsampling — O(barometer × track) on the main
/// thread. By ~15–20 minutes that work could stall Core Motion delivery
/// (also on the main queue) and trip the 90 s sensing-gap auto-end. We now
/// pick at most `maxPoints` source indices first, then resolve speeds with a
/// binary search over the time-sorted track. Recording itself also persists
/// barometer/GPS at ~1 Hz so long rides no longer accumulate 50 Hz arrays.
enum RideProfileBuilder {
    /// Default point budget for Live Activity / Watch payloads.
    static let defaultMaxPoints = 48

    static func build(
        altitudes: [AltitudeSample],
        track: [LocationSample],
        maxPoints: Int = defaultMaxPoints
    ) -> [RideProfilePoint] {
        guard maxPoints > 0 else { return [] }

        if !altitudes.isEmpty {
            return sampleIndices(count: altitudes.count, maxPoints: maxPoints).map { index in
                let sample = altitudes[index]
                return RideProfilePoint(
                    relativeAltitude: sample.relativeAltitude,
                    speedMetersPerSecond: nearestSpeed(at: sample.t, in: track)
                )
            }
        }

        if !track.isEmpty {
            // Fall back to GPS altitude when the barometer isn't available.
            let baseline = track.first?.altitude ?? 0
            return sampleIndices(count: track.count, maxPoints: maxPoints).map { index in
                let sample = track[index]
                return RideProfilePoint(
                    relativeAltitude: sample.altitude - baseline,
                    speedMetersPerSecond: sample.speed
                )
            }
        }

        return []
    }

    /// Evenly spaced indices into a source array, matching
    /// `RideLiveFormatting.downsample` endpoint retention.
    static func sampleIndices(count: Int, maxPoints: Int) -> [Int] {
        guard count > 0, maxPoints > 0 else { return [] }
        if count <= maxPoints { return Array(0..<count) }
        if maxPoints == 1 { return [count / 2] }

        var result: [Int] = []
        result.reserveCapacity(maxPoints)
        let lastIndex = count - 1
        for i in 0..<maxPoints {
            let index = Int((Double(i) * Double(lastIndex) / Double(maxPoints - 1)).rounded())
            result.append(index)
        }
        return result
    }

    /// Nearest GPS speed at `t`. Track samples are assumed sorted by `t`
    /// (append-only during a ride).
    static func nearestSpeed(at t: TimeInterval, in track: [LocationSample]) -> Double {
        guard !track.isEmpty else { return -1 }
        if track.count == 1 { return track[0].speed }

        var low = 0
        var high = track.count
        while low < high {
            let mid = (low + high) / 2
            if track[mid].t < t {
                low = mid + 1
            } else {
                high = mid
            }
        }

        if low == 0 { return track[0].speed }
        if low >= track.count { return track[track.count - 1].speed }

        let before = track[low - 1]
        let after = track[low]
        return abs(before.t - t) <= abs(after.t - t) ? before.speed : after.speed
    }
}
