import XCTest
@testable import Playground

final class RideSampleSanitizerTests: XCTestCase {
    func testReplacesNonFiniteValuesSoEncodingSucceeds() throws {
        let startedAt = Date(timeIntervalSince1970: 1_700_000_000)
        let dirty = Ride(
            id: UUID(),
            startedAt: startedAt,
            endedAt: startedAt.addingTimeInterval(60),
            durationSeconds: .nan,
            distanceMeters: .infinity,
            peakG: -.infinity,
            joltCount: 1,
            crashCount: 0,
            averageHeartRateBPM: .nan,
            events: [
                RideEvent(
                    severity: .pothole,
                    peakG: .nan,
                    at: 12,
                    latitude: .infinity,
                    longitude: -74
                )
            ],
            track: [
                LocationSample(
                    t: 0,
                    latitude: .nan,
                    longitude: -74,
                    altitude: 10,
                    horizontalAccuracy: 5,
                    verticalAccuracy: 5,
                    speed: .infinity,
                    course: 90
                )
            ],
            motion: [
                MotionSummary(t: 0, peakG: .nan, meanG: 0.2, peakRotation: 0.1, samples: 50)
            ],
            barometer: [
                AltitudeSample(t: 0, relativeAltitude: .infinity, pressureKPa: 101)
            ]
        )

        let clean = RideSampleSanitizer.sanitize(dirty)
        XCTAssertEqual(clean.durationSeconds, 0, accuracy: 0.001)
        XCTAssertEqual(clean.distanceMeters, 0, accuracy: 0.001)
        XCTAssertEqual(clean.peakG, 0, accuracy: 0.001)
        XCTAssertNil(clean.averageHeartRateBPM)
        XCTAssertEqual(clean.events.first?.peakG ?? -1, 0, accuracy: 0.001)
        XCTAssertNil(clean.events.first?.latitude)
        XCTAssertEqual(clean.track.first?.latitude ?? -1, 0, accuracy: 0.001)
        XCTAssertEqual(clean.track.first?.speed ?? 0, -1, accuracy: 0.001)
        XCTAssertEqual(clean.motion.first?.peakG ?? -1, 0, accuracy: 0.001)
        XCTAssertEqual(clean.barometer.first?.relativeAltitude ?? -1, 0, accuracy: 0.001)

        let encoder = JSONEncoder()
        encoder.dateEncodingStrategy = .iso8601
        XCTAssertNoThrow(try encoder.encode(clean))
    }

    func testPreservesEventIdentifiers() {
        let id = UUID()
        let ride = Ride(
            id: UUID(),
            startedAt: Date(),
            endedAt: Date(),
            durationSeconds: 1,
            distanceMeters: 1,
            peakG: 1,
            joltCount: 1,
            crashCount: 0,
            events: [RideEvent(id: id, severity: .impact, peakG: 3, at: 1)],
            track: [],
            motion: [],
            barometer: []
        )
        XCTAssertEqual(RideSampleSanitizer.sanitize(ride).events.first?.id, id)
    }
}
