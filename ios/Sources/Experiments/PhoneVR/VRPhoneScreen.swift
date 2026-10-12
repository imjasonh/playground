import Foundation
import simd

/// The phone's panel in the landscape orientation it has inside the viewer.
struct VRPhoneScreen: Equatable {
    /// Panel width in physical pixels; always the long edge.
    var widthPixels: Int
    /// Panel height in physical pixels; always the short edge.
    var heightPixels: Int
    var pixelsPerInch: Float

    /// Accepts either orientation of `UIScreen.nativeBounds` and stores it landscape.
    init(nativeWidth: Int, nativeHeight: Int, pixelsPerInch: Float) {
        widthPixels = max(nativeWidth, nativeHeight)
        heightPixels = min(nativeWidth, nativeHeight)
        self.pixelsPerInch = pixelsPerInch
    }

    var pixelsPerMeter: Float { pixelsPerInch / 0.0254 }
    var widthMeters: Float { Float(widthPixels) / pixelsPerMeter }
    var heightMeters: Float { Float(heightPixels) / pixelsPerMeter }
    var centerPixels: SIMD2<Float> { SIMD2(Float(widthPixels) / 2, Float(heightPixels) / 2) }

    static let iPhone15Pro = VRPhoneScreen(nativeWidth: 1179, nativeHeight: 2556, pixelsPerInch: 460)
}

/// Per-model facts that UIKit doesn't report but the optics depend on.
struct VRPhoneModel: Equatable {
    var identifier: String
    var pixelsPerInch: Float
    /// Rear wide camera position relative to the panel centre in the portrait
    /// device frame (x right, y toward the top edge, z out of the screen), meters.
    var rearCameraOffset: SIMD3<Float>

    /// iPhone 15 Pro estimate: the rear camera module centre sits about 22 mm
    /// in from the top and side edges, behind the screen-right corner as seen
    /// from the front. Other iPhones put their module in the same corner.
    static let defaultRearCameraOffset = SIMD3<Float>(0.0133, 0.0513, -0.006)

    /// Panels that differ from the 460 ppi most recent iPhones ship with.
    private static let pixelsPerInchOverrides: [String: Float] = [
        "iPhone12,1": 326, // iPhone 11
        "iPhone12,3": 458, // iPhone 11 Pro
        "iPhone12,5": 458, // iPhone 11 Pro Max
        "iPhone12,8": 326, // iPhone SE (2nd generation)
        "iPhone13,1": 476, // iPhone 12 mini
        "iPhone13,4": 458, // iPhone 12 Pro Max
        "iPhone14,3": 458, // iPhone 13 Pro Max
        "iPhone14,4": 476, // iPhone 13 mini
        "iPhone14,6": 326, // iPhone SE (3rd generation)
        "iPhone14,8": 458, // iPhone 14 Plus
    ]

    static func lookup(identifier: String, isPad: Bool) -> VRPhoneModel {
        let fallback: Float = isPad ? 264 : 460
        return VRPhoneModel(
            identifier: identifier,
            pixelsPerInch: pixelsPerInchOverrides[identifier] ?? fallback,
            rearCameraOffset: defaultRearCameraOffset
        )
    }
}

/// Which way the phone sits in the viewer, named for the side the rear camera
/// ends up on as seen by the wearer.
enum VRViewerMounting: String, Codable, CaseIterable, Identifiable {
    /// Device top on the wearer's left (`UIInterfaceOrientation.landscapeRight`).
    /// ARKit's captured image has this orientation.
    case cameraLeft
    /// Device top on the wearer's right (`UIInterfaceOrientation.landscapeLeft`).
    case cameraRight

    var id: String { rawValue }
}

/// Fixed rotations and offsets between the frames the tracker juggles.
///
/// - Device frame: Core Motion's body frame (portrait x right, y toward the top edge, z out of the screen).
/// - Camera frame: ARKit's camera (x from the top edge toward the bottom edge, y up in
///   `cameraLeft` mounting, z out of the screen).
/// - Screen frame: the landscape panel as the wearer sees it (x right, y up, z toward the
///   wearer, origin at the panel centre). The head pose is the screen frame's pose.
struct VRDeviceFrames {
    /// ARKit documents its camera x axis as pointing from the front camera toward the
    /// bottom of the device, with z out of the screen; that is the device frame turned
    /// -90° about z.
    static let deviceFromCamera = VRMath.rotationZ(-.pi / 2)

    /// Core Motion's `.xArbitraryZVertical` reference has z up; ARKit's gravity-aligned
    /// world has y up. This maps reference axes onto world axes before the unknown yaw.
    static let worldFromReferenceBase = VRMath.rotationX(-.pi / 2)

    let mounting: VRViewerMounting
    let deviceFromScreen: simd_quatf
    /// Pose of the camera in the screen frame.
    let screenFromCamera: VRPose
    /// Pose of the screen in the camera frame.
    let cameraFromScreen: VRPose

    init(mounting: VRViewerMounting, rearCameraOffset: SIMD3<Float> = VRPhoneModel.defaultRearCameraOffset) {
        self.mounting = mounting
        switch mounting {
        case .cameraLeft:
            deviceFromScreen = VRMath.rotationZ(-.pi / 2)
        case .cameraRight:
            deviceFromScreen = VRMath.rotationZ(.pi / 2)
        }
        let screenFromDevice = deviceFromScreen.inverse
        let screenFromCameraRotation = (screenFromDevice * Self.deviceFromCamera).normalized
        screenFromCamera = VRPose(
            rotation: screenFromCameraRotation,
            position: screenFromDevice.act(rearCameraOffset)
        )
        cameraFromScreen = screenFromCamera.inverse
    }

    /// World-from-reference rotation for a Core Motion yaw offset.
    static func worldFromReference(yaw: Float) -> simd_quatf {
        (VRMath.rotationY(yaw) * worldFromReferenceBase).normalized
    }
}
