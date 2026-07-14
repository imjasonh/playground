import XCTest
import CoreLocation
@testable import Playground

final class RideWeatherTests: XCTestCase {
    func testFactsLineIncludesConditionTempHumidityWind() {
        let weather = RideWeather(
            condition: "Partly Cloudy",
            symbolName: "cloud.sun",
            temperatureCelsius: 15.6,
            apparentTemperatureCelsius: 14.0,
            humidity: 0.55,
            windSpeedMetersPerSecond: 4.4704 // ~10 mph
        )
        let line = weather.factsLine
        XCTAssertTrue(line.contains("Partly Cloudy"))
        XCTAssertTrue(line.contains("16°C"))
        XCTAssertTrue(line.contains("humidity 55%"))
        XCTAssertTrue(line.contains("wind 10 mph"))
    }

    func testDisplayLineIncludesConditionAndTemperature() {
        let weather = RideWeather(
            condition: "Clear",
            symbolName: "sun.max",
            temperatureCelsius: 20,
            apparentTemperatureCelsius: nil,
            humidity: nil,
            windSpeedMetersPerSecond: nil
        )
        let line = weather.displayLine
        XCTAssertTrue(line.hasPrefix("Clear · "))
        XCTAssertFalse(line.isEmpty)
    }

    func testLocationPrefersLastTrackPoint() {
        let ride = Ride(
            id: UUID(),
            startedAt: Date(timeIntervalSince1970: 1_700_000_000),
            endedAt: Date(timeIntervalSince1970: 1_700_000_600),
            durationSeconds: 600,
            distanceMeters: 1000,
            peakG: 1.0,
            joltCount: 0,
            crashCount: 0,
            events: [],
            track: [
                LocationSample(t: 0, latitude: 40.0, longitude: -74.0, altitude: 0,
                               horizontalAccuracy: 5, verticalAccuracy: 5, speed: 1, course: 0),
                LocationSample(t: 60, latitude: 40.1, longitude: -74.1, altitude: 0,
                               horizontalAccuracy: 5, verticalAccuracy: 5, speed: 1, course: 0),
            ],
            motion: [],
            barometer: []
        )
        let location = try XCTUnwrap(RideWeatherFetcher.location(for: ride))
        XCTAssertEqual(location.coordinate.latitude, 40.1, accuracy: 0.0001)
        XCTAssertEqual(location.coordinate.longitude, -74.1, accuracy: 0.0001)
    }

    func testLocationNilWithoutTrack() {
        let ride = Ride(
            id: UUID(),
            startedAt: Date(),
            endedAt: Date().addingTimeInterval(60),
            durationSeconds: 60,
            distanceMeters: 0,
            peakG: 0,
            joltCount: 0,
            crashCount: 0,
            events: [],
            track: [],
            motion: [],
            barometer: []
        )
        XCTAssertNil(RideWeatherFetcher.location(for: ride))
    }
}
