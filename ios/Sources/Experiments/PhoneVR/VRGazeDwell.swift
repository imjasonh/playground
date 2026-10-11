import Foundation

/// Selects whatever the wearer keeps looking at for `dwellDuration`.
///
/// After a selection the same target stays quiet until the gaze leaves it or
/// `rearmDelay` passes, so staring at a `+` button repeats at a steady pace
/// instead of firing every frame.
struct VRGazeDwell<Target: Equatable> {
    var dwellDuration: TimeInterval = 1.2
    var rearmDelay: TimeInterval = 0.9

    private(set) var target: Target?
    private(set) var elapsed: TimeInterval = 0
    private var firedTarget: Target?
    private var sinceFire: TimeInterval = 0

    init(dwellDuration: TimeInterval = 1.2, rearmDelay: TimeInterval = 0.9) {
        self.dwellDuration = dwellDuration
        self.rearmDelay = rearmDelay
    }

    /// Dwell progress from 0 to 1 for the reticle ring.
    var progress: Float {
        guard let target, firedTarget != target else { return 0 }
        return Float(min(1, elapsed / dwellDuration))
    }

    /// Advances by `dt` seconds with the gaze on `newTarget`. Returns the
    /// target when its dwell completes.
    mutating func update(target newTarget: Target?, dt: TimeInterval) -> Target? {
        if newTarget != target {
            target = newTarget
            elapsed = 0
            if newTarget != firedTarget { firedTarget = nil }
        }
        guard let current = target else { return nil }
        // Frame times are summed, so allow for rounding at the threshold.
        let tolerance: TimeInterval = 1e-6
        if firedTarget == current {
            sinceFire += dt
            guard sinceFire >= rearmDelay - tolerance else { return nil }
            firedTarget = nil
            elapsed = 0
        }
        elapsed += dt
        guard elapsed >= dwellDuration - tolerance else { return nil }
        firedTarget = current
        sinceFire = 0
        elapsed = 0
        return current
    }

    mutating func reset() {
        target = nil
        elapsed = 0
        firedTarget = nil
        sinceFire = 0
    }
}
