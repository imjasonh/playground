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
        config.warmupSeconds = 0
        return SnoreDetector(config: config)
    }

    /// Sensitivity mapping with warmup disabled so tests stay short.
    private func sensitivityConfig(_ raw: Double) -> SnoreDetectorConfig {
        var config = SnoreDetectorConfig.parameters(forSensitivity: raw)
        config.warmupSeconds = 0
        return config
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
        config.warmupSeconds = 0
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
        XCTAssertGreaterThan(low.noiseFloorRiseAlpha, high.noiseFloorRiseAlpha)
        XCTAssertEqual(high.warmupSeconds, 20, accuracy: 0.01)
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

        var lowConfig = sensitivityConfig(0.1)
        lowConfig.initialNoiseFloor = quietFloor
        var insensitive = SnoreDetector(config: lowConfig)
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

        var highConfig = sensitivityConfig(0.95)
        highConfig.initialNoiseFloor = quietFloor
        var sensitive = SnoreDetector(config: highConfig)
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

    /// Quiet-bedroom levels under measurement mode: ambient ~0.001, soft snore
    /// ~0.0022. The old max-sensitivity margin (0.003) could never catch this
    /// once the floor had settled.
    func testMaxSensitivityCatchesQuietRoomSnore() throws {
        let ambient: Double = 0.001
        let snore: Double = 0.0022

        var detector = SnoreDetector(config: sensitivityConfig(1))
        // Let the seeded floor fall toward true ambient (alpha is relatively fast).
        for t in stride(from: 0.0, through: 8.0, by: 0.1) {
            _ = detector.process(rms: ambient, at: t)
        }
        for t in stride(from: 8.1, through: 9.0, by: 0.1) {
            _ = detector.process(rms: snore, at: t)
        }
        var detection: SnoreDetection?
        for t in stride(from: 9.1, through: 10.5, by: 0.1) {
            if let event = detector.process(rms: ambient, at: t) {
                detection = event
                break
            }
        }
        XCTAssertNotNil(detection, "max sensitivity should catch a soft quiet-room snore")
    }

    /// Mid sensitivity should still miss the same quiet-room snore so the
    /// slider remains meaningful.
    func testMidSensitivityMissesQuietRoomSnore() {
        let ambient: Double = 0.001
        let snore: Double = 0.0022

        var detector = SnoreDetector(config: sensitivityConfig(0.5))
        for t in stride(from: 0.0, through: 8.0, by: 0.1) {
            _ = detector.process(rms: ambient, at: t)
        }
        for t in stride(from: 8.1, through: 9.0, by: 0.1) {
            _ = detector.process(rms: snore, at: t)
        }
        for t in stride(from: 9.1, through: 10.5, by: 0.1) {
            XCTAssertNil(detector.process(rms: ambient, at: t))
        }
    }

    func testWarmupSuppressesOnsets() {
        var config = SnoreDetectorConfig.parameters(forSensitivity: 1)
        XCTAssertGreaterThan(config.warmupSeconds, 1)
        var detector = SnoreDetector(config: config)

        // Loud burst entirely inside warmup must not produce an event.
        for t in stride(from: 0.0, through: config.warmupSeconds - 0.5, by: 0.1) {
            XCTAssertNil(detector.process(rms: 0.05, at: t), "event during warmup at \(t)")
        }
        XCTAssertTrue(detector.isWarmingUp)
    }

    func testWarmupAbsorbsSteadyRoomNoise() {
        var config = SnoreDetectorConfig.parameters(forSensitivity: 1)
        var detector = SnoreDetector(config: config)
        let ambient = 0.01

        // Through warmup + a few seconds after, steady ambient alone should
        // raise the floor and not leave a stuck active event.
        var events = 0
        for t in stride(from: 0.0, through: config.warmupSeconds + 5.0, by: 0.1) {
            if detector.process(rms: ambient, at: t) != nil {
                events += 1
            }
        }
        XCTAssertEqual(events, 0, "steady room noise should be absorbed during warmup")
        XCTAssertGreaterThan(detector.noiseFloor, ambient * 0.9)
        XCTAssertGreaterThan(detector.currentThreshold, ambient)
    }

    func testApplySensitivityUpdatesThresholdLive() {
        var detector = SnoreDetector(config: sensitivityConfig(0))
        for t in stride(from: 0.0, through: 1.0, by: 0.1) {
            _ = detector.process(rms: 0.01, at: t)
        }
        let before = detector.currentThreshold
        detector.applySensitivity(1)
        let after = detector.currentThreshold
        XCTAssertLessThan(after, before)
    }

    func testMaxSensitivityMarginIsTiny() {
        let high = SnoreDetectorConfig.parameters(forSensitivity: 1)
        // Old max was 0.003 — too large for quiet-room measurement-mode RMS.
        XCTAssertLessThan(high.thresholdMargin, 0.001)
        XCTAssertLessThan(high.thresholdRatio, 0.3)
    }
}
