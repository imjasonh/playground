import XCTest
@testable import Playground

final class RideProfileBuilderTests: XCTestCase {
    func testBuildFromBarometerPairsNearestSpeed() {
        let altitudes = [
            AltitudeSample(t: 0, relativeAltitude: 0, pressureKPa: 101),
            AltitudeSample(t: 10, relativeAltitude: 5, pressureKPa: 101),
            AltitudeSample(t: 20, relativeAltitude: 2, pressureKPa: 101)
        ]
        let track = [
            LocationSample(t: 0, latitude: 0, longitude: 0, altitude: 10,
                           horizontalAccuracy: 5, verticalAccuracy: 5, speed: 1.0, course: 0),
            LocationSample(t: 12, latitude: 0, longitude: 0, altitude: 12,
                           horizontalAccuracy: 5, verticalAccuracy: 5, speed: 6.0, course: 0),
            LocationSample(t: 20, latitude: 0, longitude: 0, altitude: 11,
                           horizontalAccuracy: 5, verticalAccuracy: 5, speed: 12.0, course: 0)
        ]

        let profile = RideProfileBuilder.build(altitudes: altitudes, track: track, maxPoints: 48)
        XCTAssertEqual(profile.count, 3)
        XCTAssertEqual(profile[0].relativeAltitude, 0, accuracy: 0.001)
        XCTAssertEqual(profile[0].speedMetersPerSecond, 1.0, accuracy: 0.001)
        XCTAssertEqual(profile[1].speedMetersPerSecond, 6.0, accuracy: 0.001)
        XCTAssertEqual(profile[2].speedMetersPerSecond, 12.0, accuracy: 0.001)
    }

    func testBuildFallsBackToGPSAltitude() {
        let track = [
            LocationSample(t: 0, latitude: 0, longitude: 0, altitude: 100,
                           horizontalAccuracy: 5, verticalAccuracy: 5, speed: 3.0, course: 0),
            LocationSample(t: 5, latitude: 0, longitude: 0, altitude: 110,
                           horizontalAccuracy: 5, verticalAccuracy: 5, speed: 4.0, course: 0)
        ]

        let profile = RideProfileBuilder.build(altitudes: [], track: track)
        XCTAssertEqual(profile.count, 2)
        XCTAssertEqual(profile[0].relativeAltitude, 0, accuracy: 0.001)
        XCTAssertEqual(profile[1].relativeAltitude, 10, accuracy: 0.001)
    }

    func testDownsampleKeepsEndpoints() {
        let points = (0..<100).map {
            RideProfilePoint(relativeAltitude: Double($0), speedMetersPerSecond: Double($0) / 10)
        }
        let down = RideLiveFormatting.downsample(points, maxPoints: 5)
        XCTAssertEqual(down.count, 5)
        XCTAssertEqual(down.first?.relativeAltitude, 0, accuracy: 0.001)
        XCTAssertEqual(down.last?.relativeAltitude, 99, accuracy: 0.001)
    }

    func testEmptyInputsYieldEmptyProfile() {
        XCTAssertTrue(RideProfileBuilder.build(altitudes: [], track: []).isEmpty)
    }

    func testSpeedBuckets() {
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 0.5), 0)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 3), 1)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 7), 2)
        XCTAssertEqual(RideLiveFormatting.speedBucket(metersPerSecond: 15), 3)
    }

    func testDurationFormatting() {
        XCTAssertEqual(RideLiveSnapshot.formatDuration(65), "1:05")
        XCTAssertEqual(RideLiveSnapshot.formatDuration(3723), "1:02:03")
    }

    func testSnapshotDisplayHelpers() {
        let snapshot = RideLiveSnapshot(
            isRiding: true,
            startedAt: Date(),
            elapsedSeconds: 90,
            distanceMeters: 2500,
            currentSpeedMetersPerSecond: 5,
            profile: []
        )
        XCTAssertEqual(snapshot.formattedDuration, "1:30")
        XCTAssertEqual(snapshot.formattedDistanceKilometers, "2.50 km")
        XCTAssertEqual(snapshot.formattedSpeedKmh, "18 km/h")
    }
}
