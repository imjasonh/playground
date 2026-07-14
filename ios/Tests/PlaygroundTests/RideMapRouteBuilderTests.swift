import XCTest
import CoreLocation
@testable import Playground

final class RideMapRouteBuilderTests: XCTestCase {
    private func sample(
        lat: Double,
        lon: Double,
        speed: Double,
        t: TimeInterval = 0
    ) -> LocationSample {
        LocationSample(
            t: t,
            latitude: lat,
            longitude: lon,
            altitude: 0,
            horizontalAccuracy: 5,
            verticalAccuracy: 5,
            speed: speed,
            course: 0
        )
    }

    func testEmptyAndSinglePointProduceNoSegments() {
        XCTAssertTrue(RideMapRouteBuilder.segments(from: []).isEmpty)
        XCTAssertTrue(RideMapRouteBuilder.segments(from: [
            sample(lat: 40.0, lon: -74.0, speed: 3)
        ]).isEmpty)
    }

    func testCoalescesSameBucketIntoOneSegment() {
        // All easy (2–5 m/s).
        let track = [
            sample(lat: 40.00, lon: -74.00, speed: 3.0, t: 0),
            sample(lat: 40.01, lon: -74.00, speed: 3.5, t: 1),
            sample(lat: 40.02, lon: -74.00, speed: 4.0, t: 2),
        ]
        let segments = RideMapRouteBuilder.segments(from: track)
        XCTAssertEqual(segments.count, 1)
        XCTAssertEqual(segments[0].speedBucket, 1)
        XCTAssertEqual(segments[0].coordinates.count, 3)
    }

    func testSplitsWhenSpeedBucketChanges() {
        // slow (<2) → brisk (5–10) → fast (≥10)
        let track = [
            sample(lat: 40.00, lon: -74.00, speed: 1.0, t: 0),
            sample(lat: 40.01, lon: -74.00, speed: 6.0, t: 1),
            sample(lat: 40.02, lon: -74.00, speed: 12.0, t: 2),
            sample(lat: 40.03, lon: -74.00, speed: 12.0, t: 3),
        ]
        let segments = RideMapRouteBuilder.segments(from: track)
        XCTAssertEqual(segments.map(\.speedBucket), [0, 2, 3])
        // Each run shares the vertex with the next so the path stays continuous.
        XCTAssertEqual(segments[0].coordinates.count, 2)
        XCTAssertEqual(segments[1].coordinates.count, 2)
        XCTAssertEqual(segments[2].coordinates.count, 2)
        XCTAssertEqual(segments[0].coordinates.last?.latitude, segments[1].coordinates.first?.latitude)
        XCTAssertEqual(segments[1].coordinates.last?.latitude, segments[2].coordinates.first?.latitude)
    }

    func testInvalidSpeedTreatedAsStationary() {
        let track = [
            sample(lat: 40.00, lon: -74.00, speed: -1, t: 0),
            sample(lat: 40.01, lon: -74.00, speed: -1, t: 1),
        ]
        let segments = RideMapRouteBuilder.segments(from: track)
        XCTAssertEqual(segments.count, 1)
        XCTAssertEqual(segments[0].speedBucket, 0)
    }

    func testSkipsInvalidCoordinates() {
        let track = [
            sample(lat: 200, lon: -74.00, speed: 3.0, t: 0), // invalid lat
            sample(lat: 40.00, lon: -74.00, speed: 3.0, t: 1),
            sample(lat: 40.01, lon: -74.00, speed: 3.0, t: 2),
        ]
        let segments = RideMapRouteBuilder.segments(from: track)
        XCTAssertEqual(segments.count, 1)
        XCTAssertEqual(segments[0].coordinates.count, 2)
        XCTAssertEqual(segments[0].coordinates[0].latitude, 40.00, accuracy: 0.0001)
    }

    func testBucketsMatchLiveFormatting() {
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 0), 0)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 1.9), 0)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 2.0), 1)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 4.9), 1)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 5.0), 2)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 9.9), 2)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 10.0), 3)
    }
}
