import XCTest
@testable import Playground

final class RideMapEventFilterTests: XCTestCase {
    private func event(
        _ severity: RideSeverity,
        peakG: Double,
        at: TimeInterval,
        lat: Double? = 40.7,
        lon: Double? = -74.0
    ) -> RideEvent {
        RideEvent(severity: severity, peakG: peakG, at: at, latitude: lat, longitude: lon)
    }

    func testKeepsAllWhenUnderLimit() {
        let events = (0..<5).map { event(.pothole, peakG: 2.0 + Double($0), at: Double($0)) }
        let selected = RideMapEventFilter.selectForMap(events, limit: 10)
        XCTAssertEqual(selected.count, 5)
    }

    func testSelectsHighestPeakG() {
        var events: [RideEvent] = []
        for i in 0..<20 {
            events.append(event(.pothole, peakG: 2.0 + Double(i) * 0.1, at: Double(i)))
        }
        let selected = RideMapEventFilter.selectForMap(events, limit: 10)
        XCTAssertEqual(selected.count, 10)
        let peaks = selected.map(\.peakG).sorted(by: >)
        XCTAssertEqual(peaks.first!, 3.9, accuracy: 0.001) // 2.0 + 19*0.1
        XCTAssertEqual(peaks.last!, 3.0, accuracy: 0.001)  // 2.0 + 10*0.1
        XCTAssertFalse(selected.contains { abs($0.peakG - 2.0) < 0.001 })
    }

    func testCrashesAlwaysIncludedEvenIfSofterThanOthers() {
        var events: [RideEvent] = [
            event(.crash, peakG: 4.6, at: 1)
        ]
        for i in 0..<15 {
            events.append(event(.impact, peakG: 5.0 + Double(i), at: Double(i + 2)))
        }
        let selected = RideMapEventFilter.selectForMap(events, limit: 10)
        XCTAssertEqual(selected.filter { $0.severity == .crash }.count, 1)
        XCTAssertEqual(selected.count, 10)
        // Softest crash still kept; one of the hard impacts is dropped for it.
        XCTAssertTrue(selected.contains { $0.severity == .crash })
    }

    func testAllCrashesShownEvenAboveLimit() {
        let crashes = (0..<12).map { event(.crash, peakG: 5.0, at: Double($0)) }
        let selected = RideMapEventFilter.selectForMap(crashes, limit: 10)
        XCTAssertEqual(selected.count, 12)
        XCTAssertTrue(selected.allSatisfy { $0.severity == .crash })
    }

    func testSkipsEventsWithoutCoordinates() {
        let events = [
            event(.pothole, peakG: 3.0, at: 1, lat: nil, lon: nil),
            event(.impact, peakG: 4.0, at: 2),
            event(.pothole, peakG: 2.5, at: 3)
        ]
        let selected = RideMapEventFilter.selectForMap(events, limit: 10)
        XCTAssertEqual(selected.count, 2)
        XCTAssertFalse(selected.contains { $0.latitude == nil })
    }

    func testZeroLimitReturnsEmpty() {
        let events = [event(.pothole, peakG: 2.5, at: 1)]
        XCTAssertTrue(RideMapEventFilter.selectForMap(events, limit: 0).isEmpty)
    }
}
