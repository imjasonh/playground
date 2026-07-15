import Foundation
import ActivityKit

/// ActivityKit attributes for the Ride Monitor Live Activity.
/// Fixed `startedAt` lets the Live Activity UI drive a ticking timer without
/// a content update every second; mutable state carries distance, avg/max
/// speed, and the elevation/speed sparkline. After the ride ends, `isRiding`
/// flips false so the UI can freeze on `elapsedSeconds` instead of keeping
/// the timer alive.
struct RideMonitorAttributes: ActivityAttributes {
    /// Live values refreshed while the ride is in progress.
    struct ContentState: Codable, Hashable {
        var isRiding: Bool
        var elapsedSeconds: TimeInterval
        var distanceMeters: Double
        /// Instantaneous GPS speed in m/s (-1 when unknown). Kept for decoding
        /// continuity; Live Activity chrome shows avg + max instead.
        var currentSpeedMetersPerSecond: Double
        var averageSpeedMetersPerSecond: Double
        var maxSpeedMetersPerSecond: Double
        var profile: [RideProfilePoint]

        init(
            isRiding: Bool,
            elapsedSeconds: TimeInterval,
            distanceMeters: Double,
            currentSpeedMetersPerSecond: Double,
            averageSpeedMetersPerSecond: Double,
            maxSpeedMetersPerSecond: Double,
            profile: [RideProfilePoint]
        ) {
            self.isRiding = isRiding
            self.elapsedSeconds = elapsedSeconds
            self.distanceMeters = distanceMeters
            self.currentSpeedMetersPerSecond = currentSpeedMetersPerSecond
            self.averageSpeedMetersPerSecond = averageSpeedMetersPerSecond
            self.maxSpeedMetersPerSecond = maxSpeedMetersPerSecond
            self.profile = profile
        }

        init(snapshot: RideLiveSnapshot) {
            self.isRiding = snapshot.isRiding
            self.elapsedSeconds = snapshot.elapsedSeconds
            self.distanceMeters = snapshot.distanceMeters
            self.currentSpeedMetersPerSecond = snapshot.currentSpeedMetersPerSecond
            self.averageSpeedMetersPerSecond = snapshot.averageSpeedMetersPerSecond
            self.maxSpeedMetersPerSecond = snapshot.maxSpeedMetersPerSecond
            self.profile = snapshot.profile
        }

        var formattedDistanceMiles: String {
            String(format: "%.2f mi", RideUnits.miles(fromMeters: distanceMeters))
        }

        var formattedAverageSpeedMph: String {
            RideLiveSnapshot.formatSpeedMph(averageSpeedMetersPerSecond)
        }

        var formattedMaxSpeedMph: String {
            RideLiveSnapshot.formatSpeedMph(maxSpeedMetersPerSecond)
        }

        var formattedAverageAndMaxSpeedMph: String {
            String(
                format: "avg %.0f · max %.0f mph",
                RideUnits.milesPerHour(fromMetersPerSecond: averageSpeedMetersPerSecond),
                RideUnits.milesPerHour(fromMetersPerSecond: maxSpeedMetersPerSecond)
            )
        }

        /// Compact avg/max pair for Dynamic Island expanded trailing.
        var formattedAverageOverMaxSpeedMph: String {
            String(
                format: "%.0f / %.0f mph",
                RideUnits.milesPerHour(fromMetersPerSecond: averageSpeedMetersPerSecond),
                RideUnits.milesPerHour(fromMetersPerSecond: maxSpeedMetersPerSecond)
            )
        }

        var formattedDuration: String {
            RideLiveSnapshot.formatDuration(elapsedSeconds)
        }
    }

    /// Wall-clock start of the ride (used for the Live Activity timer).
    var startedAt: Date
}
