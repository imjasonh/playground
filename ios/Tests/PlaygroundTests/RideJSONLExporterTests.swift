import XCTest
@testable import Playground

final class RideJSONLExporterTests: XCTestCase {
    private func makeRide() -> Ride {
        let startedAt = Date(timeIntervalSince1970: 1_700_000_000)
        return Ride(
            id: UUID(uuidString: "A1B2C3D4-E5F6-7890-ABCD-EF1234567890")!,
            startedAt: startedAt,
            endedAt: startedAt.addingTimeInterval(120),
            durationSeconds: 120,
            distanceMeters: 1500,
            peakG: 2.4,
            joltCount: 1,
            crashCount: 0,
            events: [
                RideEvent(severity: .pothole, peakG: 1.8, at: 30, latitude: 40.7, longitude: -74.0)
            ],
            track: [
                LocationSample(
                    t: 0, latitude: 40.7, longitude: -74.0, altitude: 12,
                    horizontalAccuracy: 5, verticalAccuracy: 8, speed: 3.5, course: 180
                )
            ],
            motion: [
                MotionSummary(t: 1, peakG: 1.2, meanG: 0.4, peakRotation: 0.2, samples: 50)
            ],
            barometer: [
                AltitudeSample(t: 2, relativeAltitude: 1.5, pressureKPa: 101.0)
            ]
        )
    }

    func testLinesStartWithRideHeaderAndIncludeAllRecordTypes() throws {
        var ride = makeRide()
        ride.summary = "Bumpy short ride"
        let lines = try RideJSONLExporter.lines(for: ride)

        XCTAssertEqual(lines.count, 5)
        XCTAssertTrue(lines[0].contains("\"type\":\"ride\""))
        XCTAssertTrue(lines[0].contains("\"id\":\"A1B2C3D4-E5F6-7890-ABCD-EF1234567890\""))
        XCTAssertTrue(lines[0].contains("\"summary\":\"Bumpy short ride\""))
        XCTAssertTrue(lines[1].contains("\"type\":\"event\""))
        XCTAssertTrue(lines[1].contains("\"severity\":\"pothole\""))
        XCTAssertTrue(lines[2].contains("\"type\":\"location\""))
        XCTAssertTrue(lines[3].contains("\"type\":\"motion\""))
        XCTAssertTrue(lines[4].contains("\"type\":\"barometer\""))
    }

    func testDataEndsWithNewlineAndIsValidUTF8() throws {
        let data = try RideJSONLExporter.data(for: makeRide())
        XCTAssertEqual(data.last, UInt8(ascii: "\n"))

        let text = try XCTUnwrap(String(data: data, encoding: .utf8))
        let lines = text.split(separator: "\n", omittingEmptySubsequences: true)
        XCTAssertEqual(lines.count, 5)
    }

    func testExportingMultipleRidesConcatenatesBlocks() throws {
        let rideA = makeRide()
        let rideB = makeRide()
        let data = try RideJSONLExporter.data(for: [rideA, rideB])
        let text = try XCTUnwrap(String(data: data, encoding: .utf8))
        let rideHeaders = text.components(separatedBy: "\n").filter { $0.contains("\"type\":\"ride\"") }
        XCTAssertEqual(rideHeaders.count, 2)
    }

    func testLinesIncludeWatchActivityWhenPresent() throws {
        var ride = makeRide()
        ride.averageHeartRateBPM = 140
        ride.maxHeartRateBPM = 165
        ride.activeEnergyKilocalories = 88
        ride.basalEnergyKilocalories = 10
        ride.watchDistanceMeters = 1500
        ride.averageCadenceRPM = 80
        ride.averageCyclingPowerWatts = 200
        ride.maxCyclingPowerWatts = 350
        let header = try RideJSONLExporter.lines(for: ride)[0]
        XCTAssertTrue(header.contains("\"averageHeartRateBPM\":140"))
        XCTAssertTrue(header.contains("\"maxHeartRateBPM\":165"))
        XCTAssertTrue(header.contains("\"activeEnergyKilocalories\":88"))
        XCTAssertTrue(header.contains("\"basalEnergyKilocalories\":10"))
        XCTAssertTrue(header.contains("\"watchDistanceMeters\":1500"))
        XCTAssertTrue(header.contains("\"averageCadenceRPM\":80"))
        XCTAssertTrue(header.contains("\"averageCyclingPowerWatts\":200"))
        XCTAssertTrue(header.contains("\"maxCyclingPowerWatts\":350"))
    }
}
