import Foundation

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

enum DoomFaceMatcher {
    static let holdDuration: TimeInterval = 0.55
    static let captureCooldown: TimeInterval = 1.1

    static func match(_ sample: DoomFaceBlendSample) -> DoomFaceExpression? {
        if sample.eyeBlink >= 0.85, sample.jawOpen < 0.2, sample.smile < 0.2 {
            return .dead
        }
        if sample.eyeWide >= 0.55, sample.jawOpen < 0.25, sample.smile < 0.35 {
            return .god
        }
        if sample.jawOpen >= 0.45 { return .ouch }
        if sample.smile >= 0.45 { return .evil }
        if sample.browDown >= 0.4, sample.jawOpen < 0.35 { return .kill }

        let horizontal = sample.lookLeft - sample.lookRight
        let vertical = sample.lookUp - sample.lookDown
        let absH = abs(horizontal)
        let absV = abs(vertical)

        if absH >= 0.55, absH >= absV {
            return horizontal > 0 ? .turnLeft : .turnRight
        }
        if absH >= 0.28, absH >= absV {
            return horizontal > 0 ? .lookLeft : .lookRight
        }
        if absH < 0.2, absV < 0.35, sample.jawOpen < 0.25, sample.smile < 0.25 {
            return .lookCenter
        }
        return nil
    }

    struct HoldTracker {
        private(set) var current: DoomFaceExpression?
        private(set) var since: Date?
        private var lastCaptureAt: Date?

        mutating func reset() {
            current = nil
            since = nil
        }

        func progress(
            for expression: DoomFaceExpression?,
            now: Date = Date(),
            holdDuration: TimeInterval = DoomFaceMatcher.holdDuration
        ) -> Double {
            guard let expression, current == expression, let since else { return 0 }
            return min(1, max(0, now.timeIntervalSince(since) / holdDuration))
        }

        mutating func update(
            _ expression: DoomFaceExpression?,
            now: Date = Date(),
            holdDuration: TimeInterval = DoomFaceMatcher.holdDuration,
            cooldown: TimeInterval = DoomFaceMatcher.captureCooldown
        ) -> DoomFaceExpression? {
            if let lastCaptureAt, now.timeIntervalSince(lastCaptureAt) < cooldown {
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
