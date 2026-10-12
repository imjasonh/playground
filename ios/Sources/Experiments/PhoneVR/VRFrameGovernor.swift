import Foundation

/// `ProcessInfo.ThermalState`, mirrored so the policy stays testable off-device.
enum VRThermalLevel: Int, Comparable, CaseIterable {
    case nominal
    case fair
    case serious
    case critical

    static func < (a: VRThermalLevel, b: VRThermalLevel) -> Bool { a.rawValue < b.rawValue }
}

/// What the renderer runs at right now.
struct VRRenderTier: Equatable {
    var refreshRate: Int
    /// Eye-buffer pixels across the wider tangent span, per eye.
    var eyeResolution: Int
    /// True at critical temperature: fewer scene objects. Passthrough stays
    /// available because it shows the room when you leave the play area.
    var reducedScene: Bool
}

/// Picks the refresh rate and eye resolution from temperature, Low Power Mode,
/// and measured GPU time.
///
/// Thermal steps follow the sketch: nominal runs the full tier, fair drops
/// resolution, serious locks 60 Hz at 768², critical drops to a minimal scene.
/// Getting hotter applies at once; cooling down waits `coolingDelay` so tiers
/// don't oscillate. Within the thermal cap, GPU time steps the resolution
/// down when frames run long and back up after a sustained quiet stretch.
struct VRFrameGovernor {
    static let resolutionLadder = [640, 768, 896, 1024, 1152, 1280]

    struct Configuration {
        /// Highest refresh rate the wearer allows.
        var maxRefreshRate = 120
        /// Highest eye resolution the wearer allows.
        var maxEyeResolution = 1024
        /// Let GPU time move the resolution within the cap.
        var adaptiveResolution = true
        var coolingDelay: TimeInterval = 20
        /// GPU time over frame interval above which the resolution steps down.
        var highWater: Double = 0.9
        var lowWater: Double = 0.55
        var stepDownAfter: TimeInterval = 0.5
        var stepUpAfter: TimeInterval = 5
    }

    var configuration: Configuration
    private(set) var tier: VRRenderTier
    private(set) var appliedThermal: VRThermalLevel = .nominal
    private var pendingCooling: (level: VRThermalLevel, since: TimeInterval)?
    private var resolutionIndex: Int
    private var overBudgetSince: TimeInterval?
    private var underBudgetSince: TimeInterval?

    init(configuration: Configuration) {
        self.configuration = configuration
        resolutionIndex = Self.ladderIndex(atMost: configuration.maxEyeResolution)
        tier = VRRenderTier(
            refreshRate: configuration.maxRefreshRate,
            eyeResolution: Self.resolutionLadder[resolutionIndex],
            reducedScene: false
        )
    }

    static func ladderIndex(atMost resolution: Int) -> Int {
        resolutionLadder.lastIndex(where: { $0 <= resolution }) ?? 0
    }

    /// Thermal ceiling: refresh rate and ladder index.
    func cap(for level: VRThermalLevel, lowPower: Bool) -> (refreshRate: Int, resolutionIndex: Int) {
        let userIndex = Self.ladderIndex(atMost: configuration.maxEyeResolution)
        var refresh = configuration.maxRefreshRate
        var index = userIndex
        switch level {
        case .nominal:
            break
        case .fair:
            index = min(index, Self.ladderIndex(atMost: 896))
        case .serious:
            refresh = min(refresh, 60)
            index = min(index, Self.ladderIndex(atMost: 768))
        case .critical:
            refresh = min(refresh, 60)
            index = min(index, Self.ladderIndex(atMost: 640))
        }
        if lowPower { refresh = min(refresh, 60) }
        return (refresh, index)
    }

    /// Feeds one observation. Returns true when the tier changed.
    @discardableResult
    mutating func update(now: TimeInterval, thermal: VRThermalLevel, lowPower: Bool, gpuFrameTime: Double?) -> Bool {
        if thermal > appliedThermal {
            appliedThermal = thermal
            pendingCooling = nil
        } else if thermal < appliedThermal {
            if let pending = pendingCooling, pending.level == thermal {
                if now - pending.since >= configuration.coolingDelay {
                    appliedThermal = thermal
                    pendingCooling = nil
                }
            } else {
                pendingCooling = (thermal, now)
            }
        } else {
            pendingCooling = nil
        }

        let ceiling = cap(for: appliedThermal, lowPower: lowPower)
        resolutionIndex = min(resolutionIndex, ceiling.resolutionIndex)

        if configuration.adaptiveResolution, let gpu = gpuFrameTime {
            let ratio = gpu * Double(ceiling.refreshRate)
            if ratio > configuration.highWater {
                underBudgetSince = nil
                let since = overBudgetSince ?? now
                overBudgetSince = since
                if now - since >= configuration.stepDownAfter, resolutionIndex > 0 {
                    resolutionIndex -= 1
                    overBudgetSince = nil
                }
            } else if ratio < configuration.lowWater {
                overBudgetSince = nil
                let since = underBudgetSince ?? now
                underBudgetSince = since
                if now - since >= configuration.stepUpAfter, resolutionIndex < ceiling.resolutionIndex {
                    resolutionIndex += 1
                    underBudgetSince = nil
                }
            } else {
                overBudgetSince = nil
                underBudgetSince = nil
            }
        } else if !configuration.adaptiveResolution {
            resolutionIndex = ceiling.resolutionIndex
        }

        let next = VRRenderTier(
            refreshRate: ceiling.refreshRate,
            eyeResolution: Self.resolutionLadder[resolutionIndex],
            reducedScene: appliedThermal == .critical
        )
        let changed = next != tier
        tier = next
        return changed
    }
}

/// The sketch's performance budget for a refresh rate and eye resolution.
/// The splits are targets, not measurements.
struct VRFrameBudget: Equatable {
    var refreshRate: Int
    var eyeResolution: Int
    var frameIntervalMilliseconds: Double
    var gpuTotalMilliseconds: Double
    var eyePassMilliseconds: Double
    var finalPassMilliseconds: Double
    var cpuMilliseconds: Double
    var eyeMegapixelsPerFrame: Double
    var eyeMegapixelsPerSecond: Double
    var nativePanelMegapixelsPerSecond: Double
    var centerPixelsPerDegree: Double

    init(refreshRate: Int, eyeResolution: Int, bufferHalfAngleDegrees: Double = 29) {
        self.refreshRate = refreshRate
        self.eyeResolution = eyeResolution
        let hz = Double(refreshRate)
        let n = Double(eyeResolution)
        frameIntervalMilliseconds = 1000 / hz
        gpuTotalMilliseconds = frameIntervalMilliseconds * 0.8
        finalPassMilliseconds = 1.0
        eyePassMilliseconds = gpuTotalMilliseconds - finalPassMilliseconds
        cpuMilliseconds = frameIntervalMilliseconds * 0.5
        eyeMegapixelsPerFrame = 2 * n * n / 1e6
        eyeMegapixelsPerSecond = eyeMegapixelsPerFrame * hz
        nativePanelMegapixelsPerSecond = 3.01 * hz
        let halfAngle = bufferHalfAngleDegrees * .pi / 180
        centerPixelsPerDegree = n / 2 / tan(halfAngle) * .pi / 180
    }
}

/// When to read the gyro again before encoding the final pass.
///
/// The final pass can't start on the GPU until the eye pass finishes, so
/// encoding it right away wastes the time the eye pass takes. Waiting until
/// just before the GPU frees up uses a fresher rotation, as long as the final
/// pass still completes before the display deadline.
struct VRLateLatch {
    var enabled = true
    var safetyMargin: TimeInterval = 0.0015
    var encodeTime: TimeInterval = 0.0004
    var minimumWait: TimeInterval = 0.0002

    /// Seconds to wait after committing the eye pass at `now`.
    func waitDuration(
        now: TimeInterval,
        deadline: TimeInterval,
        eyePassGPUTime: TimeInterval,
        finalPassGPUTime: TimeInterval
    ) -> TimeInterval {
        guard enabled else { return 0 }
        let latest = deadline - finalPassGPUTime - encodeTime - safetyMargin
        let eyeDone = now + eyePassGPUTime - encodeTime
        let latch = min(latest, eyeDone)
        let wait = latch - now
        return wait >= minimumWait ? wait : 0
    }
}
