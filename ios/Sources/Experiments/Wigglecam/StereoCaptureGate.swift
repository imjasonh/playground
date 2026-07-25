import CoreGraphics
import Foundation

/// Pure readiness checks for Wigglecam-style stereo capture.
///
/// Capture is allowed only when the phone is in landscape and held relatively
/// level (face roughly vertical, not pitched toward the floor/sky). Thresholds
/// are intentionally forgiving so a handheld shot still works.
enum StereoCaptureGate {
    /// Max |gravity.y| while landscape (portrait tilt).
    static let maxPortraitTilt: Double = 0.22
    /// Max |gravity.z| (forward/back pitch away from vertical).
    static let maxPitch: Double = 0.28
    /// Min |gravity.x| so the long edge is mostly horizontal.
    static let minLandscapeLean: Double = 0.78

    enum Orientation: Equatable {
        case portrait
        case landscapeLeft
        case landscapeRight
        case flatOrUnknown
    }

    struct Readiness: Equatable {
        var isLandscape: Bool
        var isLevel: Bool
        var orientation: Orientation
        /// Human-readable reason when capture is blocked; empty when ready.
        var blockingReason: String

        var canCapture: Bool { isLandscape && isLevel && blockingReason.isEmpty }
    }

    /// Classify orientation from Core Motion gravity in device coordinates
    /// (+X right, +Y top, +Z toward user when held in portrait).
    static func orientation(gravityX: Double, gravityY: Double, gravityZ: Double) -> Orientation {
        let ax = abs(gravityX)
        let ay = abs(gravityY)
        let az = abs(gravityZ)
        if az > 0.75, az >= ax, az >= ay {
            return .flatOrUnknown
        }
        if ay >= ax, ay >= az {
            return .portrait
        }
        if ax >= ay, ax >= az {
            // UIKit landscapeLeft: port/home on the right → gravity pulls toward +X.
            return gravityX > 0 ? .landscapeLeft : .landscapeRight
        }
        return .flatOrUnknown
    }

    static func evaluate(gravityX: Double, gravityY: Double, gravityZ: Double) -> Readiness {
        let orientation = orientation(gravityX: gravityX, gravityY: gravityY, gravityZ: gravityZ)
        let isLandscape = orientation == .landscapeLeft || orientation == .landscapeRight
        let isLevel =
            abs(gravityY) <= maxPortraitTilt
            && abs(gravityZ) <= maxPitch
            && abs(gravityX) >= minLandscapeLean

        let reason: String
        if !isLandscape {
            switch orientation {
            case .portrait:
                reason = "Rotate to landscape."
            case .flatOrUnknown:
                reason = "Hold the phone upright in landscape."
            case .landscapeLeft, .landscapeRight:
                reason = ""
            }
        } else if !isLevel {
            reason = "Level the phone (keep it upright, not tilted)."
        } else {
            reason = ""
        }

        return Readiness(
            isLandscape: isLandscape,
            isLevel: isLevel,
            orientation: orientation,
            blockingReason: reason
        )
    }

    /// When the camera cluster is on the opposite screen edge, swap eyes so
    /// left/right stay consistent with a volume-buttons-up hold.
    static func shouldSwapEyes(for orientation: Orientation) -> Bool {
        orientation == .landscapeRight
    }
}
