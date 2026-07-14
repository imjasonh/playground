import Foundation

/// Activity samples collected on Apple Watch during a HealthKit workout
/// session, then mirrored to the phone for the live UI and saved ride.
///
/// Heart rate and active energy come from the Watch itself. Cycling distance
/// is Watch GPS (parallel to the phone track). Cadence / speed / power only
/// appear when a compatible Bluetooth sensor is paired to the Watch.
struct RideWatchActivityMetrics: Codable, Hashable, Sendable {
    /// Most recent heart rate, beats per minute.
    var heartRateBPM: Double?
    /// Average heart rate over the workout so far.
    var averageHeartRateBPM: Double?
    /// Peak heart rate over the workout so far.
    var maxHeartRateBPM: Double?
    /// Active energy burned so far, kilocalories.
    var activeEnergyKilocalories: Double?
    /// Basal energy burned so far, kilocalories.
    var basalEnergyKilocalories: Double?
    /// Watch-side cycling distance so far, meters (Watch GPS).
    var watchDistanceMeters: Double?
    /// Most recent cadence, revolutions per minute (Bluetooth sensor).
    var cadenceRPM: Double?
    /// Average cadence over the workout so far.
    var averageCadenceRPM: Double?
    /// Most recent cycling speed from a paired sensor, meters per second.
    var cyclingSpeedMetersPerSecond: Double?
    /// Most recent cycling power, watts (Bluetooth power meter).
    var cyclingPowerWatts: Double?
    /// Average cycling power over the workout so far.
    var averageCyclingPowerWatts: Double?
    /// Peak cycling power over the workout so far.
    var maxCyclingPowerWatts: Double?

    static let empty = RideWatchActivityMetrics()

    var hasAnyValue: Bool {
        heartRateBPM != nil
            || averageHeartRateBPM != nil
            || maxHeartRateBPM != nil
            || activeEnergyKilocalories != nil
            || basalEnergyKilocalories != nil
            || watchDistanceMeters != nil
            || cadenceRPM != nil
            || averageCadenceRPM != nil
            || cyclingSpeedMetersPerSecond != nil
            || cyclingPowerWatts != nil
            || averageCyclingPowerWatts != nil
            || maxCyclingPowerWatts != nil
    }

    /// Active + basal when either is present.
    var totalEnergyKilocalories: Double? {
        switch (activeEnergyKilocalories, basalEnergyKilocalories) {
        case let (active?, basal?): return active + basal
        case let (active?, nil): return active
        case let (nil, basal?): return basal
        case (nil, nil): return nil
        }
    }
}
