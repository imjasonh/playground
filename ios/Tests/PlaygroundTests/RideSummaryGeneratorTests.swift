import XCTest
@testable import Playground

final class RideSummaryGeneratorTests: XCTestCase {
    private func ride(
        durationSeconds: TimeInterval = 600,
        distanceMeters: Double = 4200,
        peakG: Double = 1.2,
        joltCount: Int = 3,
        crashCount: Int = 0,
        elevationGain: Double? = nil,
        events: [RideEvent] = []
    ) -> Ride {
        var barometer: [AltitudeSample] = []
        if let gain = elevationGain {
            barometer = [
                AltitudeSample(t: 0, relativeAltitude: 0, pressureKPa: 101),
                AltitudeSample(t: durationSeconds, relativeAltitude: gain, pressureKPa: 100.5),
            ]
        }
        return Ride(
            id: UUID(),
            startedAt: Date(timeIntervalSince1970: 1_700_000_000),
            endedAt: Date(timeIntervalSince1970: 1_700_000_000 + durationSeconds),
            durationSeconds: durationSeconds,
            distanceMeters: distanceMeters,
            peakG: peakG,
            joltCount: joltCount,
            crashCount: crashCount,
            events: events,
            track: [],
            motion: [],
            barometer: barometer
        )
    }

    func testHeuristicFlagsCrash() {
        let text = RideSummaryGenerator.heuristicSummary(for: ride(crashCount: 1))
        XCTAssertTrue(text.lowercased().contains("crash"), text)
    }

    func testHeuristicFlagsBumpyRide() {
        let text = RideSummaryGenerator.heuristicSummary(
            for: ride(durationSeconds: 300, joltCount: 20)
        )
        XCTAssertTrue(text.lowercased().contains("bumpy"), text)
    }

    func testHeuristicFlagsSmoothRide() {
        let text = RideSummaryGenerator.heuristicSummary(
            for: ride(durationSeconds: 900, distanceMeters: 8000, joltCount: 1, peakG: 0.8)
        )
        XCTAssertTrue(text.lowercased().contains("smooth"), text)
    }

    func testHeuristicFlagsClimb() {
        let text = RideSummaryGenerator.heuristicSummary(
            for: ride(elevationGain: 40)
        )
        XCTAssertTrue(text.lowercased().contains("climb"), text)
    }

    func testSanitizeTrimsQuotesAndLength() {
        let long = String(repeating: "word ", count: 20)
        let cleaned = RideSummaryGenerator.sanitize("\"\(long)\"")
        XCTAssertFalse(cleaned.contains("\""))
        XCTAssertLessThanOrEqual(cleaned.count, RideSummaryGenerator.maxLength)
    }

    func testFactsPromptIncludesCoreStats() {
        let prompt = RideSummaryGenerator.factsPrompt(
            for: ride(joltCount: 7, crashCount: 1, elevationGain: 12)
        )
        XCTAssertTrue(prompt.contains("Jolts: 7"))
        XCTAssertTrue(prompt.contains("Possible crashes: 1"))
        XCTAssertTrue(prompt.contains("Net elevation"))
    }

    func testSummarizeFallsBackToHeuristicWithoutModel() async {
        let text = await RideSummaryGenerator.summarize(for: ride(crashCount: 2))
        XCTAssertFalse(text.isEmpty)
        XCTAssertLessThanOrEqual(text.count, RideSummaryGenerator.maxLength)
    }
}
