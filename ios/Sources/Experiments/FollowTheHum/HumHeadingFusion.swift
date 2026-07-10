import Foundation

/// Fuses AirPods head yaw (relative) with a phone compass reading (true north)
/// so the hum can stay world-locked while you turn your head — even with the
/// phone in a pocket.
///
/// AirPods report attitude in an arbitrary frame. At hunt start we lock:
/// `worldOffset = phoneTrueHeading - headphoneYaw`, then
/// `headHeading = headphoneYaw + worldOffset` for the rest of the hunt.
struct HumHeadingFusion: Equatable {
    enum Source: Equatable {
        case phoneCompass
        case airPodsHead
    }

    /// Degrees to add to headphone yaw to get true-north heading. Nil until locked.
    private(set) var worldOffsetDegrees: Double?
    private(set) var lastPhoneHeadingDegrees: Double?
    private(set) var lastHeadYawDegrees: Double?
    private(set) var lastHeadHeadingDegrees: Double?
    private(set) var source: Source = .phoneCompass

    var isHeadLocked: Bool { worldOffsetDegrees != nil }

    mutating func reset() {
        worldOffsetDegrees = nil
        lastPhoneHeadingDegrees = nil
        lastHeadYawDegrees = nil
        lastHeadHeadingDegrees = nil
        source = .phoneCompass
    }

    /// Record a phone compass reading (degrees clockwise from true north).
    mutating func ingestPhoneHeading(_ degrees: Double) {
        lastPhoneHeadingDegrees = HumGeo.normalizeAngleDegrees(degrees)
        // Lock once we have both sensors; do not keep re-locking from a pocketed phone.
        tryLockIfPossible()
        refreshHeadHeading()
    }

    /// Record AirPods yaw in degrees. CoreMotion yaw is radians around vertical;
    /// callers convert before calling. Sign convention: increasing yaw = turn left
    /// in CMAttitude; we store the raw converted degrees and apply the same
    /// convention consistently with the lock.
    mutating func ingestHeadYaw(_ degrees: Double) {
        lastHeadYawDegrees = degrees
        tryLockIfPossible()
        refreshHeadHeading()
    }

    /// Best available facing direction for steering, degrees from true north.
    /// Prefers AirPods head heading once locked; otherwise phone compass.
    func facingDegrees() -> Double? {
        if let head = lastHeadHeadingDegrees, worldOffsetDegrees != nil {
            return head
        }
        return lastPhoneHeadingDegrees
    }

    func activeSource() -> Source {
        if worldOffsetDegrees != nil, lastHeadHeadingDegrees != nil {
            return .airPodsHead
        }
        return .phoneCompass
    }

    /// Pure helper: world head heading from yaw + offset.
    static func headHeadingDegrees(yaw: Double, worldOffset: Double) -> Double {
        // Normalize to [0, 360) for compass-style headings used by HumGeo.
        var value = (yaw + worldOffset).truncatingRemainder(dividingBy: 360)
        if value < 0 { value += 360 }
        return value
    }

    /// Pure helper: offset that makes `yaw + offset == phoneHeading`.
    static func worldOffsetDegrees(phoneHeading: Double, headYaw: Double) -> Double {
        HumGeo.normalizeAngleDegrees(phoneHeading - headYaw)
    }

    private mutating func tryLockIfPossible() {
        guard worldOffsetDegrees == nil,
              let phone = lastPhoneHeadingDegrees,
              let yaw = lastHeadYawDegrees else { return }
        worldOffsetDegrees = Self.worldOffsetDegrees(phoneHeading: phone, headYaw: yaw)
        source = .airPodsHead
    }

    private mutating func refreshHeadHeading() {
        guard let yaw = lastHeadYawDegrees, let offset = worldOffsetDegrees else {
            lastHeadHeadingDegrees = nil
            source = lastPhoneHeadingDegrees != nil ? .phoneCompass : source
            return
        }
        lastHeadHeadingDegrees = Self.headHeadingDegrees(yaw: yaw, worldOffset: offset)
        source = .airPodsHead
    }
}
