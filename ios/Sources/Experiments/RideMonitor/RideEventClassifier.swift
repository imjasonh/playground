import Foundation

/// Pure, dependency-free jolt/crash detection. Feed it a stream of acceleration
/// magnitudes (gravity already removed, in g) with monotonic timestamps and it
/// emits classified `RideEvent`s. No CoreMotion/CoreLocation here so it can be
/// unit-tested exhaustively without a device.
///
/// Detection model:
///  - A "burst" begins when magnitude rises above `shake` and ends when it falls
///    back below it; the burst is emitted as one event classified by its peak
///    (shake / pothole / impact). A short `debounce` after a burst suppresses
///    ringing so one bump is one event.
///  - A strong impact (peak ≥ `crashImpact`) arms a crash watch. If the phone
///    then stays still (magnitude ≤ `stillnessMax`) for `stillnessDuration`, a
///    `.crash` event is emitted. Any renewed motion cancels the watch — a rider
///    who keeps going didn't crash.
struct RideEventClassifier {
    struct Thresholds {
        var shake: Double = 0.6
        var pothole: Double = 1.2
        var impact: Double = 3.0
        var crashImpact: Double = 3.5
        var debounce: TimeInterval = 0.4
        var stillnessMax: Double = 0.15
        var stillnessDuration: TimeInterval = 3.0
    }

    var thresholds = Thresholds()

    private var inBurst = false
    private var burstPeak = 0.0
    private var burstStart = 0.0
    private var lastBurstEnd = -Double.infinity
    /// When a crash watch is armed, the time stillness began; nil when disarmed.
    private var crashArmedAt: TimeInterval?

    init(thresholds: Thresholds = Thresholds()) {
        self.thresholds = thresholds
    }

    /// Feed one sample. Returns any events detected at this sample (usually none;
    /// a jolt on burst-end, a crash after a stillness window).
    mutating func process(magnitude g: Double, at t: TimeInterval) -> [RideEvent] {
        var events: [RideEvent] = []

        if g >= thresholds.shake {
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

    private func classify(peak: Double) -> RideSeverity {
        if peak >= thresholds.impact { return .impact }
        if peak >= thresholds.pothole { return .pothole }
        return .shake
    }
}
