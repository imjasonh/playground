import Foundation
import ActivityKit

/// ActivityKit attributes for the Ride Monitor Live Activity.
/// Fixed `startedAt` lets the Live Activity UI drive a ticking timer without
/// a content update every second; mutable state carries distance, speed, and
/// the elevation/speed sparkline. After the ride ends, `isRiding` flips false
/// so the UI can freeze on `elapsedSeconds` instead of keeping the timer alive.
struct RideMonitorAttributes: ActivityAttributes {
    /// Live values refreshed while the ride is in progress.
    struct ContentState: Codable, Hashable {
        var isRiding: Bool
        var elapsedSeconds: TimeInterval
        var distanceMeters: Double
        var currentSpeedMetersPerSecond: Double
        var profile: [RideProfilePoint]

        init(
            isRiding: Bool,
            elapsedSeconds: TimeInterval,
            distanceMeters: Double,
            currentSpeedMetersPerSecond: Double,
            profile: [RideProfilePoint]
        ) {
            self.isRiding = isRiding
            self.elapsedSeconds = elapsedSeconds
            self.distanceMeters = distanceMeters
            self.currentSpeedMetersPerSecond = currentSpeedMetersPerSecond
            self.profile = profile
        }

        init(snapshot: RideLiveSnapshot) {
            self.isRiding = snapshot.isRiding
            self.elapsedSeconds = snapshot.elapsedSeconds
            self.distanceMeters = snapshot.distanceMeters
            self.currentSpeedMetersPerSecond = snapshot.currentSpeedMetersPerSecond
            self.profile = snapshot.profile
        }

        var displaySpeed: Double {
            currentSpeedMetersPerSecond >= 0 ? currentSpeedMetersPerSecond : 0
        }

        var formattedDistanceKilometers: String {
            String(format: "%.2f km", distanceMeters / 1000)
        }

        var formattedSpeedKmh: String {
            String(format: "%.0f km/h", displaySpeed * 3.6)
        }

        var formattedDuration: String {
            RideLiveSnapshot.formatDuration(elapsedSeconds)
        }
    }

    /// Wall-clock start of the ride (used for the Live Activity timer).
    var startedAt: Date
}
