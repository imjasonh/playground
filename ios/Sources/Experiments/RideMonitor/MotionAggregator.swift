import Foundation

/// Buckets the high-rate motion stream into one `MotionSummary` per whole second
/// so a saved ride stays small. Pure and unit-testable: feed samples with `add`,
/// then call `finish()` to flush the final partial second.
struct MotionAggregator {
    private var currentSecond: Int?
    private var peak = 0.0
    private var sum = 0.0
    private var peakRotation = 0.0
    private var count = 0

    /// Add a sample. Returns a summary for the previous second when the second
    /// rolls over, otherwise nil.
    mutating func add(t: TimeInterval, g: Double, rotation: Double) -> MotionSummary? {
        let second = Int(t.rounded(.down))
        var flushed: MotionSummary?

        if let current = currentSecond, second != current {
            flushed = makeSummary(second: current)
            peak = 0
            sum = 0
            peakRotation = 0
            count = 0
        }

        currentSecond = second
        peak = Swift.max(peak, g)
        sum += g
        peakRotation = Swift.max(peakRotation, rotation)
        count += 1

        return flushed
    }

    /// Flush the last in-progress second, if any.
    mutating func finish() -> MotionSummary? {
        guard count > 0, let current = currentSecond else { return nil }
        let summary = makeSummary(second: current)
        currentSecond = nil
        peak = 0
        sum = 0
        peakRotation = 0
        count = 0
        return summary
    }

    private func makeSummary(second: Int) -> MotionSummary {
        MotionSummary(
            t: TimeInterval(second),
            peakG: peak,
            meanG: count > 0 ? sum / Double(count) : 0,
            peakRotation: peakRotation,
            samples: count
        )
    }
}
