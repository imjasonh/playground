import Foundation

/// Conversions from the metric values Core Location reports (meters, m/s)
/// to the US customary units the UI displays (miles, mph).
enum RideUnits {
    static let metersPerMile = 1609.344
    static let mphPerMeterPerSecond = 2.236936

    static func miles(fromMeters meters: Double) -> Double {
        meters / metersPerMile
    }

    static func milesPerHour(fromMetersPerSecond speed: Double) -> Double {
        speed * mphPerMeterPerSecond
    }
}

/// One downsampled point on the in-progress elevation profile shown by the
/// Live Activity. Altitude is meters relative to ride start; speed is m/s
/// (negative means Core Location had no fix).
struct RideProfilePoint: Codable, Hashable, Sendable {
    var relativeAltitude: Double
    var speedMetersPerSecond: Double

    /// Treat unknown Core Location speeds as stationary for coloring.
    var displaySpeed: Double {
        speedMetersPerSecond >= 0 ? speedMetersPerSecond : 0
    }
}

/// Compact live ride stats pushed to the Live Activity and Apple Watch.
/// Kept Codable so WatchConnectivity can send it as JSON and ActivityKit
/// can embed it in `ContentState`.
struct RideLiveSnapshot: Codable, Hashable, Sendable {
    var isRiding: Bool
    var startedAt: Date
    var elapsedSeconds: TimeInterval
    var distanceMeters: Double
    /// Instantaneous GPS speed in m/s (-1 when Core Location has no reading).
    var currentSpeedMetersPerSecond: Double
    /// Overall average speed for the ride so far (`distance / elapsed`), m/s.
    var averageSpeedMetersPerSecond: Double
    /// Peak valid GPS speed seen so far this ride, m/s.
    var maxSpeedMetersPerSecond: Double
    var profile: [RideProfilePoint]

    static let idle = RideLiveSnapshot(
        isRiding: false,
        startedAt: .distantPast,
        elapsedSeconds: 0,
        distanceMeters: 0,
        currentSpeedMetersPerSecond: 0,
        averageSpeedMetersPerSecond: 0,
        maxSpeedMetersPerSecond: 0,
        profile: []
    )

    var displaySpeed: Double {
        currentSpeedMetersPerSecond >= 0 ? currentSpeedMetersPerSecond : 0
    }

    /// Formats `elapsedSeconds` as `m:ss` or `h:mm:ss`.
    var formattedDuration: String {
        Self.formatDuration(elapsedSeconds)
    }

    var formattedDistanceMiles: String {
        String(format: "%.2f mi", RideUnits.miles(fromMeters: distanceMeters))
    }

    var formattedSpeedMph: String {
        String(format: "%.0f mph", RideUnits.milesPerHour(fromMetersPerSecond: displaySpeed))
    }

    var formattedAverageSpeedMph: String {
        Self.formatSpeedMph(averageSpeedMetersPerSecond)
    }

    var formattedMaxSpeedMph: String {
        Self.formatSpeedMph(maxSpeedMetersPerSecond)
    }

    /// Compact avg + max for tight Live Activity chrome (e.g. under distance).
    var formattedAverageAndMaxSpeedMph: String {
        String(
            format: "avg %.0f · max %.0f mph",
            RideUnits.milesPerHour(fromMetersPerSecond: averageSpeedMetersPerSecond),
            RideUnits.milesPerHour(fromMetersPerSecond: maxSpeedMetersPerSecond)
        )
    }

    static func formatSpeedMph(_ metersPerSecond: Double) -> String {
        String(format: "%.0f mph", RideUnits.milesPerHour(fromMetersPerSecond: metersPerSecond))
    }

    static func formatDuration(_ interval: TimeInterval) -> String {
        let total = max(0, Int(interval.rounded()))
        let hours = total / 3600
        let minutes = (total % 3600) / 60
        let seconds = total % 60
        if hours > 0 {
            return String(format: "%d:%02d:%02d", hours, minutes, seconds)
        }
        return String(format: "%d:%02d", minutes, seconds)
    }

    /// Overall average from distance and elapsed time (includes stopped time).
    static func averageSpeed(distanceMeters: Double, elapsedSeconds: TimeInterval) -> Double {
        guard elapsedSeconds > 0, distanceMeters.isFinite, distanceMeters >= 0 else { return 0 }
        return distanceMeters / elapsedSeconds
    }
}

/// Shared formatting helpers for Live Activity + Watch chrome.
enum RideLiveFormatting {
    /// Rough speed buckets for coloring the elevation sparkline and past-ride map.
    /// 0 = crawl/slow, 1 = easy, 2 = brisk, 3 = fast.
    static func speedBucket(metersPerSecond: Double) -> Int {
        let speed = max(0, metersPerSecond)
        switch speed {
        case ..<2: return 0
        case ..<5: return 1
        case ..<10: return 2
        default: return 3
        }
    }

    static func downsample(_ points: [RideProfilePoint], maxPoints: Int) -> [RideProfilePoint] {
        guard maxPoints > 0 else { return [] }
        guard points.count > maxPoints, maxPoints > 1 else { return points }
        if maxPoints == 1 { return [points[points.count / 2]] }

        var result: [RideProfilePoint] = []
        result.reserveCapacity(maxPoints)
        let lastIndex = points.count - 1
        for i in 0..<maxPoints {
            let index = Int((Double(i) * Double(lastIndex) / Double(maxPoints - 1)).rounded())
            result.append(points[index])
        }
        return result
    }
}
