import Foundation

/// Millisecond histogram with 0.1 ms bins up to 100 ms, for medians and tails.
struct VRLatencyHistogram: Equatable {
    private(set) var bins = [Int](repeating: 0, count: 1001)
    private(set) var count = 0

    mutating func record(milliseconds: Double) {
        guard milliseconds.isFinite, milliseconds >= 0 else { return }
        let index = min(bins.count - 1, Int((milliseconds * 10).rounded()))
        bins[index] += 1
        count += 1
    }

    /// Value at quantile `q` (0 to 1), or nil when empty.
    func quantile(_ q: Double) -> Double? {
        guard count > 0 else { return nil }
        let target = max(1, Int((Double(count) * q).rounded(.up)))
        var seen = 0
        for (i, n) in bins.enumerated() {
            seen += n
            if seen >= target { return Double(i) / 10 }
        }
        return Double(bins.count - 1) / 10
    }
}

/// Exponential moving average for on-headset readouts.
struct VRSmoothedValue: Equatable {
    var smoothing: Double = 0.1
    private(set) var value: Double?

    init(smoothing: Double = 0.1) {
        self.smoothing = smoothing
    }

    mutating func add(_ sample: Double) {
        guard sample.isFinite else { return }
        if let value {
            self.value = value + (sample - value) * smoothing
        } else {
            value = sample
        }
    }
}

/// What a VR session measured, shown after you leave the headset.
struct VRSessionSummary: Codable, Equatable {
    var endedAt: Date
    var duration: TimeInterval
    var frames: Int
    var missedFrames: Int
    var averageFrameRate: Double
    var eyePassMedianMilliseconds: Double?
    var eyePassP95Milliseconds: Double?
    var finalPassMedianMilliseconds: Double?
    var finalPassP95Milliseconds: Double?
    var cpuMedianMilliseconds: Double?
    /// Presentation time minus the gyro sample the final pass used.
    var photonLatencyMedianMilliseconds: Double?
    var photonLatencyP95Milliseconds: Double?
    var sixDoFFraction: Double
    var hottestThermalLevel: Int
    var lowestEyeResolution: Int
    var highestEyeResolution: Int
    var viewerSlips: Int
    var airPodsLatencyMilliseconds: Double?
}

/// Per-frame bookkeeping on the render thread, turned into a summary at exit.
struct VRFrameStatistics {
    private(set) var frames = 0
    private(set) var missedFrames = 0
    private(set) var sixDoFFrames = 0
    private var firstPresentation: TimeInterval?
    private var lastPresentation: TimeInterval?
    private(set) var eyePass = VRLatencyHistogram()
    private(set) var finalPass = VRLatencyHistogram()
    private(set) var cpu = VRLatencyHistogram()
    private(set) var photonLatency = VRLatencyHistogram()
    private(set) var hottest: VRThermalLevel = .nominal
    private(set) var lowestResolution = Int.max
    private(set) var highestResolution = 0

    var smoothedFrameInterval = VRSmoothedValue(smoothing: 0.05)
    var smoothedEyePass = VRSmoothedValue(smoothing: 0.05)
    var smoothedFinalPass = VRSmoothedValue(smoothing: 0.05)
    var smoothedCPU = VRSmoothedValue(smoothing: 0.05)
    var smoothedPhotonLatency = VRSmoothedValue(smoothing: 0.05)

    /// Records a frame the display link asked for. `expectedInterval` is the
    /// refresh period; a gap of more than 1.5 of them counts as a missed frame.
    mutating func recordFrame(
        presentationTime: TimeInterval,
        expectedInterval: TimeInterval,
        cpuMilliseconds: Double,
        mode: VRTrackingMode,
        thermal: VRThermalLevel,
        eyeResolution: Int
    ) {
        frames += 1
        if mode == .sixDoF { sixDoFFrames += 1 }
        if let last = lastPresentation {
            let interval = presentationTime - last
            if interval > 0 {
                smoothedFrameInterval.add(interval)
                if interval > expectedInterval * 1.5 {
                    missedFrames += max(1, Int((interval / expectedInterval).rounded()) - 1)
                }
            }
        }
        if firstPresentation == nil { firstPresentation = presentationTime }
        lastPresentation = presentationTime
        cpu.record(milliseconds: cpuMilliseconds)
        smoothedCPU.add(cpuMilliseconds)
        hottest = max(hottest, thermal)
        lowestResolution = min(lowestResolution, eyeResolution)
        highestResolution = max(highestResolution, eyeResolution)
    }

    mutating func recordGPU(eyePassMilliseconds: Double?, finalPassMilliseconds: Double?) {
        if let eye = eyePassMilliseconds {
            eyePass.record(milliseconds: eye)
            smoothedEyePass.add(eye)
        }
        if let final = finalPassMilliseconds {
            finalPass.record(milliseconds: final)
            smoothedFinalPass.add(final)
        }
    }

    mutating func recordPhotonLatency(milliseconds: Double) {
        guard milliseconds > 0, milliseconds < 200 else { return }
        photonLatency.record(milliseconds: milliseconds)
        smoothedPhotonLatency.add(milliseconds)
    }

    func summary(endedAt: Date, slips: Int, airPodsLatency: Double?) -> VRSessionSummary {
        let duration = max(0, (lastPresentation ?? 0) - (firstPresentation ?? 0))
        return VRSessionSummary(
            endedAt: endedAt,
            duration: duration,
            frames: frames,
            missedFrames: missedFrames,
            averageFrameRate: duration > 0 ? Double(frames - 1) / duration : 0,
            eyePassMedianMilliseconds: eyePass.quantile(0.5),
            eyePassP95Milliseconds: eyePass.quantile(0.95),
            finalPassMedianMilliseconds: finalPass.quantile(0.5),
            finalPassP95Milliseconds: finalPass.quantile(0.95),
            cpuMedianMilliseconds: cpu.quantile(0.5),
            photonLatencyMedianMilliseconds: photonLatency.quantile(0.5),
            photonLatencyP95Milliseconds: photonLatency.quantile(0.95),
            sixDoFFraction: frames > 0 ? Double(sixDoFFrames) / Double(frames) : 0,
            hottestThermalLevel: hottest.rawValue,
            lowestEyeResolution: lowestResolution == Int.max ? 0 : lowestResolution,
            highestEyeResolution: highestResolution,
            viewerSlips: slips,
            airPodsLatencyMilliseconds: airPodsLatency.map { $0 * 1000 }
        )
    }
}
