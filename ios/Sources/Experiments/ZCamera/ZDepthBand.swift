import Foundation

/// A depth interval in meters. Either bound may be `.infinity` (no clip on that side).
///
/// Visibility rule: a finite depth `d` is shown when `near ≤ d ≤ far`.
/// Invalid / non-finite depths are always outside the band.
struct ZDepthBand: Equatable, Sendable {
    enum Bound: Equatable, Sendable {
        case meters(Double)
        case infinity

        /// Finite meter value, or `nil` for infinity.
        var finiteMeters: Double? {
            switch self {
            case .meters(let meters): return meters
            case .infinity: return nil
            }
        }

        static func label(_ bound: Bound) -> String {
            switch bound {
            case .infinity:
                return "∞"
            case .meters(let meters):
                if meters < 0.005 { return "0 m" }
                if meters < 1 {
                    return String(format: "%.0f cm", meters * 100)
                }
                return String(format: "%.2f m", meters)
            }
        }

        /// Total order for clamp/compare: every finite value is less than infinity.
        static func <= (lhs: Bound, rhs: Bound) -> Bool {
            switch (lhs, rhs) {
            case (.infinity, .infinity):
                return true
            case (.infinity, .meters):
                return false
            case (.meters, .infinity):
                return true
            case (.meters(let a), .meters(let b)):
                return a <= b
            }
        }
    }

    var near: Bound
    var far: Bound

    /// Default band: show everything the depth camera can measure.
    static let open = ZDepthBand(near: .meters(0), far: .infinity)

    /// Whether a depth sample in meters falls inside the band.
    func contains(_ depthMeters: Double) -> Bool {
        guard depthMeters.isFinite, depthMeters >= 0 else { return false }

        switch near {
        case .infinity:
            // Nothing finite is ≥ ∞.
            return false
        case .meters(let nearMeters):
            guard depthMeters >= nearMeters else { return false }
        }

        switch far {
        case .infinity:
            return true
        case .meters(let farMeters):
            return depthMeters <= farMeters
        }
    }

    /// Ensures `near ≤ far` by pulling the moved edge back if needed.
    func clamped() -> ZDepthBand {
        if near <= far { return self }
        // Prefer preserving `far` when the interval collapses.
        return ZDepthBand(near: far, far: far)
    }
}

/// Maps a unit slider `0...1` onto a depth bound, with `1` meaning infinity.
enum ZDepthSliderMapping {
    /// Finite depths on the slider span `0...finiteCapMeters`; the top stop is ∞.
    static let finiteCapMeters: Double = 8.0

    static func bound(sliderValue: Double) -> ZDepthBand.Bound {
        let clamped = min(1, max(0, sliderValue))
        if clamped >= 1 - 1e-9 {
            return .infinity
        }
        return .meters(clamped * finiteCapMeters)
    }

    static func sliderValue(for bound: ZDepthBand.Bound) -> Double {
        switch bound {
        case .infinity:
            return 1
        case .meters(let meters):
            guard finiteCapMeters > 0 else { return 0 }
            return min(1, max(0, meters / finiteCapMeters))
        }
    }
}
