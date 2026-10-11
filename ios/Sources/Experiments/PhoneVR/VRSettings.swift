import Foundation

/// Everything the wearer can tune, persisted between launches.
struct PhoneVRSettings: Codable, Equatable {
    enum RefreshRate: String, Codable, CaseIterable, Identifiable {
        case automatic
        case hz120
        case hz60

        var id: String { rawValue }

        var title: String {
            switch self {
            case .automatic: return "Automatic"
            case .hz120: return "120 Hz"
            case .hz60: return "60 Hz"
            }
        }

        var maximum: Int { self == .hz60 ? 60 : 120 }
    }

    enum EyeResolution: String, Codable, CaseIterable, Identifiable {
        case automatic
        case r768
        case r1024
        case r1280

        var id: String { rawValue }

        var title: String {
            switch self {
            case .automatic: return "Automatic"
            case .r768: return "768²"
            case .r1024: return "1024²"
            case .r1280: return "1280²"
            }
        }

        /// Largest eye resolution allowed, and whether GPU time may lower it.
        var cap: (resolution: Int, adaptive: Bool) {
            switch self {
            case .automatic: return (1024, true)
            case .r768: return (768, false)
            case .r1024: return (1024, false)
            case .r1280: return (1280, false)
            }
        }
    }

    enum Tracking: String, Codable, CaseIterable, Identifiable {
        /// ARKit world tracking for position plus the gyro for rotation.
        case sixDoF
        /// Gyro only, with the camera off. Less heat, slow yaw drift.
        case threeDoF

        var id: String { rawValue }

        var title: String {
            switch self {
            case .sixDoF: return "6DoF (camera)"
            case .threeDoF: return "3DoF (camera off)"
            }
        }
    }

    var profile: VRViewerProfile = .standard
    var mounting: VRViewerMounting = .cameraLeft
    var refreshRate: RefreshRate = .automatic
    var eyeResolution: EyeResolution = .automatic
    var tracking: Tracking = .sixDoF
    var multisampling = true
    var singlePassStereo = true
    var prediction = true
    var lateLatch = true
    var timewarp = true
    var chromaticCorrection = true
    var spatialAudio = true
    var airPodsCrossCheck = false
    var comfortVignette = true
    var snapTurnDegrees: Float = 30
    var locomotionSpeed: Float = 1.4
    var playAreaRadius: Float = 1.5
    var eyeHeight: Float = 1.6
    var showStats = false
    var metalPerformanceHUD = false
    var countdownSeconds: Double = 5

    init() {}

    private enum CodingKeys: String, CodingKey {
        case profile, mounting, refreshRate, eyeResolution, tracking, multisampling
        case singlePassStereo, prediction, lateLatch, timewarp, chromaticCorrection
        case spatialAudio, airPodsCrossCheck, comfortVignette, snapTurnDegrees
        case locomotionSpeed, playAreaRadius, eyeHeight, showStats, metalPerformanceHUD
        case countdownSeconds
    }

    /// Missing keys keep their defaults, so settings saved by older builds still load.
    init(from decoder: Decoder) throws {
        let c = try decoder.container(keyedBy: CodingKeys.self)
        let d = PhoneVRSettings()
        profile = try c.decodeIfPresent(VRViewerProfile.self, forKey: .profile) ?? d.profile
        mounting = try c.decodeIfPresent(VRViewerMounting.self, forKey: .mounting) ?? d.mounting
        refreshRate = try c.decodeIfPresent(RefreshRate.self, forKey: .refreshRate) ?? d.refreshRate
        eyeResolution = try c.decodeIfPresent(EyeResolution.self, forKey: .eyeResolution) ?? d.eyeResolution
        tracking = try c.decodeIfPresent(Tracking.self, forKey: .tracking) ?? d.tracking
        multisampling = try c.decodeIfPresent(Bool.self, forKey: .multisampling) ?? d.multisampling
        singlePassStereo = try c.decodeIfPresent(Bool.self, forKey: .singlePassStereo) ?? d.singlePassStereo
        prediction = try c.decodeIfPresent(Bool.self, forKey: .prediction) ?? d.prediction
        lateLatch = try c.decodeIfPresent(Bool.self, forKey: .lateLatch) ?? d.lateLatch
        timewarp = try c.decodeIfPresent(Bool.self, forKey: .timewarp) ?? d.timewarp
        chromaticCorrection = try c.decodeIfPresent(Bool.self, forKey: .chromaticCorrection) ?? d.chromaticCorrection
        spatialAudio = try c.decodeIfPresent(Bool.self, forKey: .spatialAudio) ?? d.spatialAudio
        airPodsCrossCheck = try c.decodeIfPresent(Bool.self, forKey: .airPodsCrossCheck) ?? d.airPodsCrossCheck
        comfortVignette = try c.decodeIfPresent(Bool.self, forKey: .comfortVignette) ?? d.comfortVignette
        snapTurnDegrees = try c.decodeIfPresent(Float.self, forKey: .snapTurnDegrees) ?? d.snapTurnDegrees
        locomotionSpeed = try c.decodeIfPresent(Float.self, forKey: .locomotionSpeed) ?? d.locomotionSpeed
        playAreaRadius = try c.decodeIfPresent(Float.self, forKey: .playAreaRadius) ?? d.playAreaRadius
        eyeHeight = try c.decodeIfPresent(Float.self, forKey: .eyeHeight) ?? d.eyeHeight
        showStats = try c.decodeIfPresent(Bool.self, forKey: .showStats) ?? d.showStats
        metalPerformanceHUD = try c.decodeIfPresent(Bool.self, forKey: .metalPerformanceHUD) ?? d.metalPerformanceHUD
        countdownSeconds = try c.decodeIfPresent(Double.self, forKey: .countdownSeconds) ?? d.countdownSeconds
    }

    func governorConfiguration() -> VRFrameGovernor.Configuration {
        var configuration = VRFrameGovernor.Configuration()
        configuration.maxRefreshRate = refreshRate.maximum
        configuration.maxEyeResolution = eyeResolution.cap.resolution
        configuration.adaptiveResolution = eyeResolution.cap.adaptive
        return configuration
    }
}
