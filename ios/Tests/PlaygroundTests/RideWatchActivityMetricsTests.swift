import XCTest
@testable import Playground

final class RideWatchActivityMetricsTests: XCTestCase {
    func testEmptyHasNoValues() {
        XCTAssertFalse(RideWatchActivityMetrics.empty.hasAnyValue)
        XCTAssertNil(RideWatchActivityMetrics.empty.totalEnergyKilocalories)
    }

    func testTotalEnergySumsActiveAndBasal() {
        var metrics = RideWatchActivityMetrics.empty
        metrics.activeEnergyKilocalories = 100
        metrics.basalEnergyKilocalories = 25
        XCTAssertEqual(metrics.totalEnergyKilocalories ?? 0, 125, accuracy: 0.001)
    }

    func testCodableRoundTrip() throws {
        let metrics = RideWatchActivityMetrics(
            heartRateBPM: 150,
            averageHeartRateBPM: 138,
            maxHeartRateBPM: 172,
            activeEnergyKilocalories: 90.25,
            basalEnergyKilocalories: 12.5,
            watchDistanceMeters: 3200,
            cadenceRPM: 84,
            averageCadenceRPM: 78,
            cyclingSpeedMetersPerSecond: 6.5,
            cyclingPowerWatts: 210,
            averageCyclingPowerWatts: 185,
            maxCyclingPowerWatts: 450
        )
        let data = try JSONEncoder().encode(metrics)
        let decoded = try JSONDecoder().decode(RideWatchActivityMetrics.self, from: data)
        XCTAssertEqual(decoded.heartRateBPM ?? 0, 150, accuracy: 0.001)
        XCTAssertEqual(decoded.watchDistanceMeters ?? 0, 3200, accuracy: 0.001)
        XCTAssertEqual(decoded.averageCadenceRPM ?? 0, 78, accuracy: 0.001)
        XCTAssertEqual(decoded.maxCyclingPowerWatts ?? 0, 450, accuracy: 0.001)
        XCTAssertEqual(decoded.totalEnergyKilocalories ?? 0, 102.75, accuracy: 0.001)
        XCTAssertTrue(decoded.hasAnyValue)
    }
}
