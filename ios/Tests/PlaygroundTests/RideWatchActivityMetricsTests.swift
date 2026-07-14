import XCTest
@testable import Playground

final class RideWatchActivityMetricsTests: XCTestCase {
    func testEmptyHasNoValues() {
        XCTAssertFalse(RideWatchActivityMetrics.empty.hasAnyValue)
    }

    func testCodableRoundTrip() throws {
        let metrics = RideWatchActivityMetrics(
            heartRateBPM: 150,
            averageHeartRateBPM: 138,
            maxHeartRateBPM: 172,
            activeEnergyKilocalories: 90.25
        )
        let data = try JSONEncoder().encode(metrics)
        let decoded = try JSONDecoder().decode(RideWatchActivityMetrics.self, from: data)
        XCTAssertEqual(decoded.heartRateBPM ?? 0, 150, accuracy: 0.001)
        XCTAssertEqual(decoded.averageHeartRateBPM ?? 0, 138, accuracy: 0.001)
        XCTAssertEqual(decoded.maxHeartRateBPM ?? 0, 172, accuracy: 0.001)
        XCTAssertEqual(decoded.activeEnergyKilocalories ?? 0, 90.25, accuracy: 0.001)
        XCTAssertTrue(decoded.hasAnyValue)
    }
}
