import Foundation

/// Configuration for level-based snore onset detection.
///
/// Snoring is treated as a sustained loudness spike above a slowly adapting
/// ambient noise floor. This is intentionally simple for v1; spectral / ML
/// classifiers can replace `process(rms:at:)` later without changing the
/// monitor or store.
struct SnoreDetectorConfig: Equatable {
    /// How quickly the ambient floor tracks quiet audio (0…1 per sample).
    var noiseFloorAlpha: Double = 0.02
    /// How quickly the floor rises toward louder audio (kept slow so snores
    /// don't immediately become the new baseline).
    var noiseFloorRiseAlpha: Double = 0.002
    /// Trigger when RMS exceeds `noiseFloor + max(margin, floor * ratio)`.
    var thresholdRatio: Double = 2.5
    var thresholdMargin: Double = 0.015
    /// Minimum time the level must stay above threshold to start an event.
    var minAboveSeconds: TimeInterval = 0.35
    /// Level must stay below threshold this long to end an event.
    var endBelowSeconds: TimeInterval = 0.6
    /// Ignore new onsets this long after the previous event ends.
    var cooldownSeconds: TimeInterval = 4.0
    /// Hard cap so a continuous noise source can't produce a huge clip.
    var maxEventSeconds: TimeInterval = 12.0
    /// Seed floor so the first moments aren't hypersensitive.
    var initialNoiseFloor: Double = 0.008
}

/// One confirmed loudness event candidate ready to be clipped from the ring buffer.
struct SnoreDetection: Equatable {
    /// Session-relative time when the level first crossed threshold.
    let startedAt: TimeInterval
    /// Session-relative time when the event ended (quiet resumed or max length).
    let endedAt: TimeInterval
    /// Peak RMS observed during the event.
    let peakRMS: Double
    /// Ambient noise floor at the moment of onset.
    let noiseFloorAtOnset: Double

    var duration: TimeInterval { endedAt - startedAt }
}

/// Pure stateful detector: feed periodic RMS readings, receive completed events.
struct SnoreDetector {
    var config: SnoreDetectorConfig

    private(set) var noiseFloor: Double
    private var aboveSince: TimeInterval?
    private var belowSince: TimeInterval?
    private var activeStart: TimeInterval?
    private var activePeak: Double = 0
    private var floorAtOnset: Double = 0
    private var cooldownUntil: TimeInterval = 0
    private var lastTime: TimeInterval = 0

    init(config: SnoreDetectorConfig = SnoreDetectorConfig()) {
        self.config = config
        self.noiseFloor = config.initialNoiseFloor
    }

    mutating func reset() {
        noiseFloor = config.initialNoiseFloor
        aboveSince = nil
        belowSince = nil
        activeStart = nil
        activePeak = 0
        floorAtOnset = 0
        cooldownUntil = 0
        lastTime = 0
    }

    /// Process one RMS window. Returns a detection when an event completes.
    mutating func process(rms: Double, at time: TimeInterval) -> SnoreDetection? {
        lastTime = time
        let level = max(0, rms)
        updateNoiseFloor(level)

        let threshold = noiseFloor + max(config.thresholdMargin, noiseFloor * config.thresholdRatio)
        let isAbove = level >= threshold

        if let start = activeStart {
            activePeak = max(activePeak, level)
            if isAbove {
                belowSince = nil
                if time - start >= config.maxEventSeconds {
                    return finishEvent(at: time)
                }
                return nil
            }
            if belowSince == nil { belowSince = time }
            if let quietStart = belowSince, time - quietStart >= config.endBelowSeconds {
                return finishEvent(at: quietStart)
            }
            return nil
        }

        // Idle: look for a sustained rise above threshold (after cooldown).
        guard time >= cooldownUntil else {
            aboveSince = nil
            return nil
        }

        if isAbove {
            if aboveSince == nil {
                aboveSince = time
                floorAtOnset = noiseFloor
            }
            activePeak = max(activePeak, level)
            if let since = aboveSince, time - since >= config.minAboveSeconds {
                activeStart = since
                aboveSince = nil
                belowSince = nil
            }
        } else {
            aboveSince = nil
            activePeak = 0
        }
        return nil
    }

    /// Force-close any in-flight event (e.g. session stop).
    mutating func flush(at time: TimeInterval? = nil) -> SnoreDetection? {
        guard activeStart != nil else { return nil }
        return finishEvent(at: time ?? lastTime)
    }

    private mutating func updateNoiseFloor(_ level: Double) {
        if level <= noiseFloor {
            noiseFloor += (level - noiseFloor) * config.noiseFloorAlpha
        } else if activeStart == nil {
            // Rise slowly while idle so a brief snore doesn't raise the floor.
            noiseFloor += (level - noiseFloor) * config.noiseFloorRiseAlpha
        }
        noiseFloor = max(0.0005, noiseFloor)
    }

    private mutating func finishEvent(at end: TimeInterval) -> SnoreDetection? {
        guard let start = activeStart else { return nil }
        let ended = max(start, end)
        let detection = SnoreDetection(
            startedAt: start,
            endedAt: ended,
            peakRMS: activePeak,
            noiseFloorAtOnset: floorAtOnset
        )
        activeStart = nil
        aboveSince = nil
        belowSince = nil
        activePeak = 0
        cooldownUntil = ended + config.cooldownSeconds
        return detection
    }

    /// Threshold currently in effect (for UI metering).
    var currentThreshold: Double {
        noiseFloor + max(config.thresholdMargin, noiseFloor * config.thresholdRatio)
    }
}
