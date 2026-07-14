import Foundation

/// Configuration for level-based snore onset detection.
///
/// Snoring is treated as a sustained loudness spike above a slowly adapting
/// ambient noise floor. This is intentionally simple for v1; spectral / ML
/// classifiers can replace `process(rms:at:)` later without changing the
/// monitor or store.
struct SnoreDetectorConfig: Equatable {
    /// How quickly the ambient floor tracks quiet audio (0…1 per sample).
    var noiseFloorAlpha: Double = 0.05
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
    /// Seed floor so the first moments aren't hypersensitive. Falls quickly
    /// toward true ambient via `noiseFloorAlpha`.
    var initialNoiseFloor: Double = 0.008
    /// Ignore onsets while the floor is still calibrating to the room.
    /// Production sensitivity configs set this; raw configs default to 0 so
    /// unit tests stay short.
    var warmupSeconds: TimeInterval = 0

    /// Default slider position — biased toward catching quiet snoring; drag
    /// down if room noise false-triggers.
    static let defaultSensitivity: Double = 0.85

    /// Maps a 0…1 sensitivity slider to detector thresholds.
    ///
    /// Higher sensitivity → lower ratio/margin and a shorter sustain requirement,
    /// so quieter / shorter bursts still trigger. Ratio and margin interpolate in
    /// log space so the upper half of the slider is actually useful in quiet
    /// rooms — a linear map left max sensitivity with margin 0.003, which needs
    /// ~4× ambient and missed overnight snoring even at 100%.
    static func parameters(forSensitivity raw: Double) -> SnoreDetectorConfig {
        let s = min(1, max(0, raw))
        var config = SnoreDetectorConfig()
        // Least sensitive (0): ratio 3.5, margin 0.025, minAbove 0.50s
        // Most sensitive (1):  ratio 0.18, margin 0.0003, minAbove 0.12s
        config.thresholdRatio = Self.lerpLog(from: 3.5, to: 0.18, t: s)
        config.thresholdMargin = Self.lerpLog(from: 0.025, to: 0.0003, t: s)
        config.minAboveSeconds = 0.50 - s * 0.38
        // At high sensitivity, rise the floor more slowly so soft intermittent
        // snoring doesn't become the new baseline.
        config.noiseFloorRiseAlpha = 0.0025 - s * 0.0018
        // Let the seeded floor fall/rise toward true ambient before onsets count.
        config.warmupSeconds = 20
        return config
    }

    /// Logarithmic interpolation — equal slider steps feel like equal loudness
    /// factors rather than equal absolute RMS deltas.
    private static func lerpLog(from a: Double, to b: Double, t: Double) -> Double {
        a * pow(b / a, t)
    }
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

    /// Swap threshold parameters without resetting noise-floor state — used when
    /// the sensitivity slider moves mid-session.
    mutating func applySensitivity(_ sensitivity: Double) {
        let next = SnoreDetectorConfig.parameters(forSensitivity: sensitivity)
        config.thresholdRatio = next.thresholdRatio
        config.thresholdMargin = next.thresholdMargin
        config.minAboveSeconds = next.minAboveSeconds
        config.noiseFloorRiseAlpha = next.noiseFloorRiseAlpha
        // Keep the existing warmup deadline — don't restart calibration mid-session.
        if config.warmupSeconds == 0 {
            config.warmupSeconds = next.warmupSeconds
        }
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

        // Idle: look for a sustained rise above threshold (after warmup + cooldown).
        let onsetGate = max(cooldownUntil, config.warmupSeconds)
        guard time >= onsetGate else {
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
            // During warmup, chase steady room noise quickly so HVAC / fans
            // become the floor before onsets count. Afterward, rise slowly so
            // real snores don't immediately become the baseline.
            let rise: Double
            if lastTime < config.warmupSeconds {
                rise = max(config.noiseFloorRiseAlpha, 0.06)
            } else {
                rise = config.noiseFloorRiseAlpha
            }
            noiseFloor += (level - noiseFloor) * rise
        }
        noiseFloor = max(0.0002, noiseFloor)
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

    /// True while onsets are suppressed so the ambient floor can settle.
    var isWarmingUp: Bool {
        lastTime < config.warmupSeconds
    }
}
