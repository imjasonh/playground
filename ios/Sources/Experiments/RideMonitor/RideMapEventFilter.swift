import Foundation

/// Picks which ride events to pin on the map. Recording still keeps every
/// detected jolt in the ride file; the map only shows the biggest ones so a
/// rough ride doesn't become a sea of pins.
enum RideMapEventFilter {
    /// Default pin budget for `RideMapView`.
    static let defaultLimit = 10

    /// Returns up to `limit` mappable events, preferring crashes then highest peak g.
    /// Crashes are never dropped to satisfy the limit — a ride with more crashes
    /// than `limit` still shows every crash pin.
    static func selectForMap(_ events: [RideEvent], limit: Int = defaultLimit) -> [RideEvent] {
        let mappable = events.filter { $0.latitude != nil && $0.longitude != nil }
        guard limit > 0 else { return [] }
        guard mappable.count > limit else { return mappable }

        let crashes = mappable.filter { $0.severity == .crash }
        if crashes.count >= limit {
            return crashes
        }

        let others = mappable
            .filter { $0.severity != .crash }
            .sorted { lhs, rhs in
                if lhs.peakG != rhs.peakG { return lhs.peakG > rhs.peakG }
                return lhs.at < rhs.at
            }

        return crashes + Array(others.prefix(limit - crashes.count))
    }
}
