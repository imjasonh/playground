import Foundation

/// Heart rate / energy collected on Apple Watch during a HealthKit workout
/// session, then mirrored to the phone for the live UI and saved ride.
struct RideWatchActivityMetrics: Codable, Hashable, Sendable {
    /// Most recent heart rate, beats per minute.
    var heartRateBPM: Double?
    /// Average heart rate over the workout so far.
    var averageHeartRateBPM: Double?
    /// Peak heart rate over the workout so far.
    var maxHeartRateBPM: Double?
    /// Active energy burned so far, kilocalories.
    var activeEnergyKilocalories: Double?

    static let empty = RideWatchActivityMetrics()

    var hasAnyValue: Bool {
        heartRateBPM != nil
            || averageHeartRateBPM != nil
            || maxHeartRateBPM != nil
            || activeEnergyKilocalories != nil
    }
}
