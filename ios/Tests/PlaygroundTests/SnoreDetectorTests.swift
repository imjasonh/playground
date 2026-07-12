import XCTest
@testable import Playground

final class SnoreDetectorTests: XCTestCase {
    private func makeDetector() -> SnoreDetector {
        var config = SnoreDetectorConfig()
        config.initialNoiseFloor = 0.01
        config.thresholdRatio = 2.0
        config.thresholdMargin = 0.01
        config.minAboveSeconds = 0.3
        config.endBelowSeconds = 0.4
        config.cooldownSeconds = 1.0
        config.maxEventSeconds = 5.0
        config.noiseFloorAlpha = 0.05
        config.noiseFloorRiseAlpha = 0.001
        return SnoreDetector(config: config)
    }

    func testQuietAudioProducesNoEvents() {
        var detector = makeDetector()
        for t in stride(from: 0.0, through: 5.0, by: 0.1) {
            let event = detector.process(rms: 0.008, at: t)
            XCTAssertNil(event, "unexpected event at \(t)")
        }
    }

    func testSustainedLoudnessProducesOneEvent() throws {
        var detector = makeDetector()
        // Establish floor.
        for t in stride(from: 0.0, through: 1.0, by: 0.1) {
            XCTAssertNil(detector.process(rms: 0.01, at: t))
        }
        // Loud burst.
        for t in stride(from: 1.1, through: 2.0, by: 0.1) {
            XCTAssertNil(detector.process(rms: 0.08, at: t))
        }
        // Return to quiet long enough to close the event.
        var detection: SnoreDetection?
        for t in stride(from: 2.1, through: 3.0, by: 0.1) {
            if let event = detector.process(rms: 0.01, at: t) {
                detection = event
                break
            }
        }
        let event = try XCTUnwrap(detection)
        XCTAssertEqual(event.startedAt, 1.1, accuracy: 0.05)
        XCTAssertGreaterThan(event.duration, 0.5)
        XCTAssertGreaterThan(event.peakRMS, 0.05)
    }

    func testBriefSpikeIsIgnored() {
        var detector = makeDetector()
        for t in stride(from: 0.0, through: 1.0, by: 0.1) {
            _ = detector.process(rms: 0.01, at: t)
        }
        // 0.2s spike — under minAboveSeconds (0.3).
        XCTAssertNil(detector.process(rms: 0.09, at: 1.1))
        XCTAssertNil(detector.process(rms: 0.09, at: 1.2))
        XCTAssertNil(detector.process(rms: 0.01, at: 1.3))
        XCTAssertNil(detector.process(rms: 0.01, at: 2.0))
    }

    func testCooldownSuppressesImmediateSecondEvent() throws {
        var detector = makeDetector()
        for t in stride(from: 0.0, through: 1.0, by: 0.1) {
            _ = detector.process(rms: 0.01, at: t)
        }
        for t in stride(from: 1.1, through: 2.0, by: 0.1) {
            _ = detector.process(rms: 0.08, at: t)
        }
        var first: SnoreDetection?
        for t in stride(from: 2.1, through: 3.0, by: 0.1) {
            if let event = detector.process(rms: 0.01, at: t) {
                first = event
                break
            }
        }
        let ended = try XCTUnwrap(first).endedAt

        // Burst fully inside the cooldown window must not produce an event.
        let burstStart = ended + 0.1
        let burstEnd = ended + 0.8 // cooldown is 1.0s
        for t in stride(from: burstStart, through: burstEnd, by: 0.1) {
            XCTAssertNil(detector.process(rms: 0.09, at: t), "event during cooldown at \(t)")
        }
        for t in stride(from: burstEnd + 0.1, through: ended + 1.5, by: 0.1) {
            XCTAssertNil(detector.process(rms: 0.01, at: t), "late event at \(t)")
        }
    }

    func testFlushClosesActiveEvent() throws {
        var detector = makeDetector()
        for t in stride(from: 0.0, through: 1.0, by: 0.1) {
            _ = detector.process(rms: 0.01, at: t)
        }
        for t in stride(from: 1.1, through: 1.8, by: 0.1) {
            _ = detector.process(rms: 0.08, at: t)
        }
        let event = try XCTUnwrap(detector.flush(at: 1.8))
        XCTAssertEqual(event.endedAt, 1.8, accuracy: 0.001)
        XCTAssertNil(detector.flush(at: 2.0))
    }

    func testMaxEventSecondsForceEnds() throws {
        var config = SnoreDetectorConfig()
        config.initialNoiseFloor = 0.01
        config.thresholdRatio = 2.0
        config.thresholdMargin = 0.01
        config.minAboveSeconds = 0.2
        config.maxEventSeconds = 1.0
        config.endBelowSeconds = 5.0
        config.noiseFloorRiseAlpha = 0.0001
        var detector = SnoreDetector(config: config)

        for t in stride(from: 0.0, through: 0.5, by: 0.1) {
            _ = detector.process(rms: 0.01, at: t)
        }
        var detection: SnoreDetection?
        for t in stride(from: 0.6, through: 3.0, by: 0.1) {
            if let event = detector.process(rms: 0.1, at: t) {
                detection = event
                break
            }
        }
        let event = try XCTUnwrap(detection)
        XCTAssertEqual(event.duration, 1.0, accuracy: 0.15)
    }

    func testSensitivityMappingIsMonotonic() {
        let low = SnoreDetectorConfig.parameters(forSensitivity: 0)
        let mid = SnoreDetectorConfig.parameters(forSensitivity: 0.5)
        let high = SnoreDetectorConfig.parameters(forSensitivity: 1)

        XCTAssertGreaterThan(low.thresholdRatio, mid.thresholdRatio)
        XCTAssertGreaterThan(mid.thresholdRatio, high.thresholdRatio)
        XCTAssertGreaterThan(low.thresholdMargin, mid.thresholdMargin)
        XCTAssertGreaterThan(mid.thresholdMargin, high.thresholdMargin)
        XCTAssertGreaterThan(low.minAboveSeconds, high.minAboveSeconds)
    }

    func testSensitivityClampsOutOfRange() {
        let below = SnoreDetectorConfig.parameters(forSensitivity: -1)
        let above = SnoreDetectorConfig.parameters(forSensitivity: 2)
        XCTAssertEqual(below, SnoreDetectorConfig.parameters(forSensitivity: 0))
        XCTAssertEqual(above, SnoreDetectorConfig.parameters(forSensitivity: 1))
    }

    func testHigherSensitivityDetectsQuieterBurst() throws {
        // Moderate burst that only high sensitivity should catch.
        let quietFloor: Double = 0.01
        let burst: Double = 0.028

        var insensitive = SnoreDetector(config: .parameters(forSensitivity: 0.1))
        for t in stride(from: 0.0, through: 1.0, by: 0.1) {
            _ = insensitive.process(rms: quietFloor, at: t)
        }
        for t in stride(from: 1.1, through: 2.2, by: 0.1) {
            _ = insensitive.process(rms: burst, at: t)
        }
        var lowDetection: SnoreDetection?
        for t in stride(from: 2.3, through: 3.5, by: 0.1) {
            if let event = insensitive.process(rms: quietFloor, at: t) {
                lowDetection = event
                break
            }
        }
        XCTAssertNil(lowDetection, "low sensitivity should ignore a mild burst")

        var sensitive = SnoreDetector(config: .parameters(forSensitivity: 0.95))
        for t in stride(from: 0.0, through: 1.0, by: 0.1) {
            _ = sensitive.process(rms: quietFloor, at: t)
        }
        for t in stride(from: 1.1, through: 2.2, by: 0.1) {
            _ = sensitive.process(rms: burst, at: t)
        }
        var highDetection: SnoreDetection?
        for t in stride(from: 2.3, through: 3.5, by: 0.1) {
            if let event = sensitive.process(rms: quietFloor, at: t) {
                highDetection = event
                break
            }
        }
        XCTAssertNotNil(highDetection, "high sensitivity should catch the mild burst")
    }

    func testApplySensitivityUpdatesThresholdLive() {
        var detector = SnoreDetector(config: .parameters(forSensitivity: 0))
        for t in stride(from: 0.0, through: 1.0, by: 0.1) {
            _ = detector.process(rms: 0.01, at: t)
        }
        let before = detector.currentThreshold
        detector.applySensitivity(1)
        let after = detector.currentThreshold
        XCTAssertLessThan(after, before)
    }
}
