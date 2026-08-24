import Foundation

/// ARKit blend-shape sample used to pick a doom face expression.
struct DoomFaceBlendSample: Equatable {
    var lookLeft: Double
    var lookRight: Double
    var lookUp: Double
    var lookDown: Double
    var jawOpen: Double
    var smile: Double
    var browDown: Double
    var eyeWide: Double
    var eyeBlink: Double

    static let zero = DoomFaceBlendSample(
        lookLeft: 0, lookRight: 0, lookUp: 0, lookDown: 0,
        jawOpen: 0, smile: 0, browDown: 0, eyeWide: 0, eyeBlink: 0
    )
}

/// Maps live face blend shapes onto sheet expressions.
enum DoomFaceMatcher {
    /// How long an expression must stay stable before we capture.
    static let holdDuration: TimeInterval = 0.55
    /// Ignore re-matches briefly after a successful capture.
    static let captureCooldown: TimeInterval = 1.1

    /// Classify the strongest matching expression, or `nil` if nothing stands out.
    static func match(_ sample: DoomFaceBlendSample) -> DoomFaceExpression? {
        // Specials first — rare, high thresholds.
        if sample.eyeBlink >= 0.85, sample.jawOpen < 0.2, sample.smile < 0.2 {
            return .dead
        }
        if sample.eyeWide >= 0.55, sample.jawOpen < 0.25, sample.smile < 0.35 {
            return .god
        }

        if sample.jawOpen >= 0.45 {
            return .ouch
        }
        if sample.smile >= 0.45 {
            return .evil
        }
        if sample.browDown >= 0.4, sample.jawOpen < 0.35 {
            return .kill
        }

        let horizontal = sample.lookLeft - sample.lookRight
        let vertical = sample.lookUp - sample.lookDown
        let absH = abs(horizontal)
        let absV = abs(vertical)

        // Hard turns when looking far sideways.
        if absH >= 0.55, absH >= absV {
            return horizontal > 0 ? .turnLeft : .turnRight
        }
        if absH >= 0.28, absH >= absV {
            return horizontal > 0 ? .lookLeft : .lookRight
        }

        // Neutral gaze → center stare.
        if absH < 0.2, absV < 0.35, sample.jawOpen < 0.25, sample.smile < 0.25 {
            return .lookCenter
        }

        return nil
    }

    /// Tracks hold time so a fleeting twitch does not stamp a face.
    struct HoldTracker {
        private(set) var current: DoomFaceExpression?
        private(set) var since: Date?
        private var lastCaptureAt: Date?

        mutating func reset() {
            current = nil
            since = nil
        }

        /// 0…1 progress toward a capture for the current expression.
        func progress(
            for expression: DoomFaceExpression?,
            now: Date = Date(),
            holdDuration: TimeInterval = DoomFaceMatcher.holdDuration
        ) -> Double {
            guard let expression, current == expression, let since else { return 0 }
            return min(1, max(0, now.timeIntervalSince(since) / holdDuration))
        }

        /// Returns an expression once it has been held long enough and cooldown allows.
        mutating func update(
            _ expression: DoomFaceExpression?,
            now: Date = Date(),
            holdDuration: TimeInterval = DoomFaceMatcher.holdDuration,
            cooldown: TimeInterval = DoomFaceMatcher.captureCooldown
        ) -> DoomFaceExpression? {
            if let lastCaptureAt, now.timeIntervalSince(lastCaptureAt) < cooldown {
                // Still cooling down — keep tracking the live expression for UI, but
                // don't accumulate hold time toward another capture yet.
                if current != expression {
                    current = expression
                    since = nil
                }
                return nil
            }

            guard let expression else {
                reset()
                return nil
            }

            if current != expression || since == nil {
                current = expression
                since = now
                return nil
            }

            guard let since, now.timeIntervalSince(since) >= holdDuration else {
                return nil
            }

            lastCaptureAt = now
            self.since = nil
            return expression
        }
    }
}
