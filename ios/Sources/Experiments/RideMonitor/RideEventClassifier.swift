import Foundation

/// Pure, dependency-free jolt/crash detection. Feed it a stream of acceleration
/// magnitudes (gravity already removed, in g) with monotonic timestamps and it
/// emits classified `RideEvent`s. No CoreMotion/CoreLocation here so it can be
/// unit-tested exhaustively without a device.
///
/// Detection model:
///  - A "burst" begins when magnitude rises above `pothole` and ends when it
///    falls back below it; the burst is emitted as one event classified by its
///    peak (pothole / impact). Anything below the pothole floor — hand shakes,
///    road buzz, pocket jostling — is not recorded at all. A short `debounce`
///    after a burst suppresses ringing so one bump is one event.
///  - A strong impact (peak ≥ `crashImpact`) arms a crash watch. If the phone
///    then stays still (magnitude ≤ `stillnessMax`) for `stillnessDuration`, a
///    `.crash` event is emitted. Any renewed motion cancels the watch — a rider
///    who keeps going didn't crash.
///  - A long gap between samples (app suspended / sensors paused) flushes any
///    open burst via `flushOpenBurst` and clears the crash watch — stillness
///    across a suspend is not a crash, and the caller must geolocate flushed
///    events with the *pre-gap* location.
struct RideEventClassifier {
    struct Thresholds {
        /// Recording floor. Bike/scooter road buzz and hand shakes sit around
        /// 0.5–1.0g; anything below this is ignored entirely (shakes used to be
        /// recorded above 0.85g and triggered far too easily).
        var pothole: Double = 1.5
        var impact: Double = 3.5
        var crashImpact: Double = 4.0
        /// Collapse ringing from one physical bump into a single event.
        var debounce: TimeInterval = 0.8
        var stillnessMax: Double = 0.15
        var stillnessDuration: TimeInterval = 3.0
        /// Sample spacing above this is treated as a sensing gap (50 Hz → 0.02s).
        var maxSampleGap: TimeInterval = 2.0
    }

    var thresholds = Thresholds()

    private var inBurst = false
    private var burstPeak = 0.0
    private var burstStart = 0.0
    private var lastBurstEnd = -Double.infinity
    /// When a crash watch is armed, the time stillness began; nil when disarmed.
    private var crashArmedAt: TimeInterval?
    private var lastSampleAt: TimeInterval?

    init(thresholds: Thresholds = Thresholds()) {
        self.thresholds = thresholds
    }

    /// Feed one sample. Returns any events detected at this sample (usually none;
    /// a jolt on burst-end, a crash after a stillness window).
    ///
    /// Call `flushOpenBurst(endingAt:)` yourself when you observe a sensing gap
    /// *before* feeding the first post-gap sample, so the flushed event can be
    /// tagged with the pre-gap GPS fix.
    mutating func process(magnitude g: Double, at t: TimeInterval) -> [RideEvent] {
        var events: [RideEvent] = []

        if let last = lastSampleAt, t - last > thresholds.maxSampleGap {
            // Caller should have flushed already; belt-and-suspenders reset.
            events += flushOpenBurst(endingAt: last)
        }

        lastSampleAt = t

        if g >= thresholds.pothole {
            if inBurst {
                burstPeak = max(burstPeak, g)
            } else if t - lastBurstEnd >= thresholds.debounce {
                inBurst = true
                burstPeak = g
                burstStart = t
            }
        } else if inBurst {
            inBurst = false
            lastBurstEnd = t
            let severity = classify(peak: burstPeak)
            events.append(RideEvent(severity: severity, peakG: burstPeak, at: burstStart))
            crashArmedAt = burstPeak >= thresholds.crashImpact ? t : nil
        }

        if let armedAt = crashArmedAt {
            if g > thresholds.stillnessMax {
                crashArmedAt = nil // motion resumed → not a crash
            } else if t - armedAt >= thresholds.stillnessDuration {
                events.append(RideEvent(severity: .crash, peakG: burstPeak, at: t))
                crashArmedAt = nil
            }
        }

        return events
    }

    /// Close an in-progress burst after a sensing gap. Clears any crash watch
    /// (suspend ≠ crash). Returns at most one jolt event.
    mutating func flushOpenBurst(endingAt t: TimeInterval) -> [RideEvent] {
        crashArmedAt = nil
        guard inBurst else {
            lastSampleAt = t
            return []
        }
        inBurst = false
        lastBurstEnd = t
        lastSampleAt = t
        let severity = classify(peak: burstPeak)
        return [RideEvent(severity: severity, peakG: burstPeak, at: burstStart)]
    }

    private func classify(peak: Double) -> RideSeverity {
        peak >= thresholds.impact ? .impact : .pothole
    }
}
