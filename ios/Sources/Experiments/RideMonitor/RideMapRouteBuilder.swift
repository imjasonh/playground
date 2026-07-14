import Foundation
import CoreLocation

/// One contiguous stretch of a ride track drawn in a single speed-bucket color.
struct RideMapRouteSegment: Equatable {
    /// Same buckets as `RideLiveFormatting.speedBucket` (0 slow … 3 fast).
    let speedBucket: Int
    let coordinates: [CLLocationCoordinate2D]

    static func == (lhs: RideMapRouteSegment, rhs: RideMapRouteSegment) -> Bool {
        guard lhs.speedBucket == rhs.speedBucket,
              lhs.coordinates.count == rhs.coordinates.count else { return false }
        return zip(lhs.coordinates, rhs.coordinates).allSatisfy {
            $0.latitude == $1.latitude && $0.longitude == $1.longitude
        }
    }
}

/// Splits a GPS track into polylines colored by the same speed buckets as the
/// Live Activity elevation sparkline (slow / easy / brisk / fast).
enum RideMapRouteBuilder {
    /// Build coalesced segments from consecutive fixes. Each edge `i → i+1` is
    /// colored by the speed at point `i` (invalid CL speeds count as 0), matching
    /// `RideElevationProfileView`. Runs of the same bucket become one segment.
    static func segments(from track: [LocationSample]) -> [RideMapRouteSegment] {
        let points: [(coord: CLLocationCoordinate2D, speed: Double)] = track.compactMap { sample in
            let coord = CLLocationCoordinate2D(latitude: sample.latitude, longitude: sample.longitude)
            guard CLLocationCoordinate2DIsValid(coord) else { return nil }
            let speed = sample.speed >= 0 ? sample.speed : 0
            return (coord, speed)
        }
        guard points.count >= 2 else { return [] }

        var result: [RideMapRouteSegment] = []
        var currentBucket = RideLiveFormatting.speedBucket(metersPerSecond: points[0].speed)
        var currentCoords: [CLLocationCoordinate2D] = [points[0].coord]

        for i in 0..<(points.count - 1) {
            let bucket = RideLiveFormatting.speedBucket(metersPerSecond: points[i].speed)
            let next = points[i + 1].coord
            if bucket == currentBucket {
                currentCoords.append(next)
            } else {
                if currentCoords.count >= 2 {
                    result.append(RideMapRouteSegment(speedBucket: currentBucket, coordinates: currentCoords))
                }
                // Start the new run at the shared vertex so the path stays continuous.
                currentBucket = bucket
                currentCoords = [points[i].coord, next]
            }
        }

        if currentCoords.count >= 2 {
            result.append(RideMapRouteSegment(speedBucket: currentBucket, coordinates: currentCoords))
        }
        return result
    }
}
