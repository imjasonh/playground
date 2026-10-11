import ARKit
import CoreMotion
import Metal
import UIKit

/// What this device offers phone VR.
struct PhoneVRDeviceInfo: Equatable {
    var modelIdentifier: String
    var model: VRPhoneModel
    var screen: VRPhoneScreen
    var maximumFramesPerSecond: Int
    var isPad: Bool
    var supportsWorldTracking: Bool
    var hasLiDAR: Bool
    var gpuName: String?
    var supportsSinglePassStereo: Bool
    var supportsHeadphoneMotion: Bool

    @MainActor
    static func current() -> PhoneVRDeviceInfo {
        let identifier = modelIdentifier()
        let isPad = UIDevice.current.userInterfaceIdiom == .pad
        let model = VRPhoneModel.lookup(identifier: identifier, isPad: isPad)
        let screen = activeScreen()
        let native = screen?.nativeBounds.size ?? CGSize(width: 1179, height: 2556)
        let device = MTLCreateSystemDefaultDevice()
        return PhoneVRDeviceInfo(
            modelIdentifier: identifier,
            model: model,
            screen: VRPhoneScreen(nativeWidth: Int(native.width), nativeHeight: Int(native.height), pixelsPerInch: model.pixelsPerInch),
            maximumFramesPerSecond: screen?.maximumFramesPerSecond ?? 60,
            isPad: isPad,
            supportsWorldTracking: ARWorldTrackingConfiguration.isSupported,
            hasLiDAR: ARWorldTrackingConfiguration.supportsSceneReconstruction(.mesh),
            gpuName: device?.name,
            supportsSinglePassStereo: device.map(VRRenderer.supportsSinglePassStereo) ?? false,
            supportsHeadphoneMotion: CMHeadphoneMotionManager().isDeviceMotionAvailable
        )
    }

    @MainActor
    static func activeScreen() -> UIScreen? {
        let scenes = UIApplication.shared.connectedScenes.compactMap { $0 as? UIWindowScene }
        return (scenes.first { $0.activationState == .foregroundActive } ?? scenes.first)?.screen
    }

    /// Hardware model such as "iPhone16,1" (iPhone 15 Pro). The Simulator
    /// reports the model it simulates.
    static func modelIdentifier() -> String {
        if let simulated = ProcessInfo.processInfo.environment["SIMULATOR_MODEL_IDENTIFIER"] { return simulated }
        var info = utsname()
        uname(&info)
        return withUnsafeBytes(of: info.machine) { bytes in
            String(decoding: bytes.prefix { $0 != 0 }, as: UTF8.self)
        }
    }
}
