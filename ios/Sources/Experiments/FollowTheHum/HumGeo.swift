import Foundation
import CoreLocation

/// Pure geographic helpers for Follow the Hum. Kept free of UIKit/AVFoundation
/// so unit tests can exercise hide-spot generation and steering math on Linux CI
/// and in the iOS simulator without hardware.
enum HumGeo {
    /// Earth radius in meters (WGS84 mean).
    static let earthRadiusMeters: Double = 6_371_000

    /// Shortest signed difference from `from` to `to` in degrees, in (-180, 180].
    static func normalizeAngleDegrees(_ degrees: Double) -> Double {
        var value = degrees.truncatingRemainder(dividingBy: 360)
        if value <= -180 { value += 360 }
        if value > 180 { value -= 360 }
        return value
    }

    /// Initial bearing from `from` to `to`, degrees clockwise from true north [0, 360).
    static func bearingDegrees(from: CLLocationCoordinate2D, to: CLLocationCoordinate2D) -> Double {
        let φ1 = from.latitude * .pi / 180
        let φ2 = to.latitude * .pi / 180
        let Δλ = (to.longitude - from.longitude) * .pi / 180

        let y = sin(Δλ) * cos(φ2)
        let x = cos(φ1) * sin(φ2) - sin(φ1) * cos(φ2) * cos(Δλ)
        let θ = atan2(y, x) * 180 / .pi
        return (θ + 360).truncatingRemainder(dividingBy: 360)
    }

    /// Great-circle distance in meters.
    static func distanceMeters(from: CLLocationCoordinate2D, to: CLLocationCoordinate2D) -> Double {
        let φ1 = from.latitude * .pi / 180
        let φ2 = to.latitude * .pi / 180
        let Δφ = (to.latitude - from.latitude) * .pi / 180
        let Δλ = (to.longitude - from.longitude) * .pi / 180

        let a = sin(Δφ / 2) * sin(Δφ / 2)
            + cos(φ1) * cos(φ2) * sin(Δλ / 2) * sin(Δλ / 2)
        let c = 2 * atan2(sqrt(a), sqrt(1 - a))
        return earthRadiusMeters * c
    }

    /// Destination coordinate after traveling `distanceMeters` along `bearingDegrees`
    /// from `from` (degrees clockwise from true north).
    static func destination(
        from: CLLocationCoordinate2D,
        bearingDegrees: Double,
        distanceMeters: Double
    ) -> CLLocationCoordinate2D {
        let δ = distanceMeters / earthRadiusMeters
        let θ = bearingDegrees * .pi / 180
        let φ1 = from.latitude * .pi / 180
        let λ1 = from.longitude * .pi / 180

        let sinφ2 = sin(φ1) * cos(δ) + cos(φ1) * sin(δ) * cos(θ)
        let φ2 = asin(sinφ2)
        let λ2 = λ1 + atan2(
            sin(θ) * sin(δ) * cos(φ1),
            cos(δ) - sin(φ1) * sinφ2
        )

        return CLLocationCoordinate2D(
            latitude: φ2 * 180 / .pi,
            longitude: normalizeLongitude(λ2 * 180 / .pi)
        )
    }

    /// Bearing of the target relative to the device heading, degrees in (-180, 180].
    /// 0 = ahead, +90 = right ear, -90 = left ear, ±180 = behind.
    static func relativeBearingDegrees(targetBearing: Double, heading: Double) -> Double {
        normalizeAngleDegrees(targetBearing - heading)
    }

    /// Pick a hidden walkable spot: random bearing, distance uniformly in
    /// `[minDistance, maxDistance]` meters from `origin`.
    static func hideSpot(
        from origin: CLLocationCoordinate2D,
        minDistanceMeters: Double,
        maxDistanceMeters: Double,
        randomBearing: () -> Double = { Double.random(in: 0..<360) },
        randomUnit: () -> Double = { Double.random(in: 0...1) }
    ) -> CLLocationCoordinate2D {
        precondition(minDistanceMeters > 0)
        precondition(maxDistanceMeters >= minDistanceMeters)
        let t = randomUnit()
        let distance = minDistanceMeters + t * (maxDistanceMeters - minDistanceMeters)
        return destination(
            from: origin,
            bearingDegrees: randomBearing(),
            distanceMeters: distance
        )
    }

    private static func normalizeLongitude(_ degrees: Double) -> Double {
        var value = degrees.truncatingRemainder(dividingBy: 360)
        if value <= -180 { value += 360 }
        if value > 180 { value -= 360 }
        return value
    }
}
