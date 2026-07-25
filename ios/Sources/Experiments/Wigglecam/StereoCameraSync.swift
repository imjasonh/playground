import AVFoundation
import CoreGraphics

/// Capture-time exposure / white-balance helpers for DualWide MultiCam.
///
/// Apple’s DualWide virtual device already drives constituent AE/AWB/AF in
/// tandem when configured on the **virtual** device (not each constituent).
/// DualWide also forbids custom ISO/duration and custom WB gains — only
/// lock-to-current. We therefore:
/// 1. Force shared **center** metering so both eyes expose for the same region
/// 2. **Freeze** AE/AWB/AF at shutter so the pair can’t diverge mid-grab
/// 3. Restore continuous auto after the still is taken
enum StereoCameraSync {
    /// Normalized point-of-interest used for exposure + focus (image coords).
    static let sharedMeteringPoint = CGPoint(x: 0.5, y: 0.5)

    /// Center metering + continuous auto for live preview.
    static func applySharedMeteringAndContinuousAuto(to device: AVCaptureDevice) throws {
        try device.lockForConfiguration()
        defer { device.unlockForConfiguration() }

        if device.isFocusPointOfInterestSupported {
            device.focusPointOfInterest = sharedMeteringPoint
        }
        if device.isExposurePointOfInterestSupported {
            device.exposurePointOfInterest = sharedMeteringPoint
        }

        if device.isFocusModeSupported(.continuousAutoFocus) {
            device.focusMode = .continuousAutoFocus
        }
        if device.isExposureModeSupported(.continuousAutoExposure) {
            device.exposureMode = .continuousAutoExposure
        }
        if device.isWhiteBalanceModeSupported(.continuousAutoWhiteBalance) {
            device.whiteBalanceMode = .continuousAutoWhiteBalance
        }
    }

    /// Wait for AE/AWB to settle (best-effort), then lock to current values.
    /// Call on the session queue before requesting a still frame.
    static func lockForStereoStill(
        _ device: AVCaptureDevice,
        settleTimeout: TimeInterval = 0.35,
        postLockSettle: TimeInterval = 0.05
    ) throws {
        waitForAdjustmentsToSettle(device, timeout: settleTimeout)

        try device.lockForConfiguration()
        defer { device.unlockForConfiguration() }

        if device.isFocusPointOfInterestSupported {
            device.focusPointOfInterest = sharedMeteringPoint
        }
        if device.isExposurePointOfInterestSupported {
            device.exposurePointOfInterest = sharedMeteringPoint
        }

        // DualWide: only current lens position / current WB gains are legal.
        if device.isFocusModeSupported(.locked) {
            device.focusMode = .locked
        }
        if device.isExposureModeSupported(.locked) {
            device.exposureMode = .locked
        }
        if device.isWhiteBalanceModeSupported(.locked) {
            // Prefer locking the live gains when the device allows it; DualWide
            // virtual devices typically only accept "current".
            if device.isLockingWhiteBalanceWithCustomDeviceGainsSupported {
                let clamped = clampWhiteBalanceGains(
                    device.deviceWhiteBalanceGains,
                    maxGain: device.maxWhiteBalanceGain
                )
                device.setWhiteBalanceModeLocked(with: clamped, completionHandler: nil)
            } else {
                device.setWhiteBalanceModeLocked(
                    with: AVCaptureDevice.currentWhiteBalanceGains,
                    completionHandler: nil
                )
            }
        }

        if postLockSettle > 0 {
            Thread.sleep(forTimeInterval: postLockSettle)
        }
    }

    /// Resume continuous auto after a still capture.
    static func unlockContinuousAuto(_ device: AVCaptureDevice) {
        guard (try? device.lockForConfiguration()) != nil else { return }
        defer { device.unlockForConfiguration() }

        if device.isFocusPointOfInterestSupported {
            device.focusPointOfInterest = sharedMeteringPoint
        }
        if device.isExposurePointOfInterestSupported {
            device.exposurePointOfInterest = sharedMeteringPoint
        }
        if device.isFocusModeSupported(.continuousAutoFocus) {
            device.focusMode = .continuousAutoFocus
        }
        if device.isExposureModeSupported(.continuousAutoExposure) {
            device.exposureMode = .continuousAutoExposure
        }
        if device.isWhiteBalanceModeSupported(.continuousAutoWhiteBalance) {
            device.whiteBalanceMode = .continuousAutoWhiteBalance
        }
    }

    /// Clamp each WB channel into `[1, maxGain]` (AVFoundation requirement).
    static func clampWhiteBalanceGains(
        _ gains: AVCaptureDevice.WhiteBalanceGains,
        maxGain: Float
    ) -> AVCaptureDevice.WhiteBalanceGains {
        let lo: Float = 1
        let hi = max(lo, maxGain)
        return AVCaptureDevice.WhiteBalanceGains(
            redGain: min(max(gains.redGain, lo), hi),
            greenGain: min(max(gains.greenGain, lo), hi),
            blueGain: min(max(gains.blueGain, lo), hi)
        )
    }

    /// Pure helper for tests: clamp ISO into a format’s legal range.
    static func clampISO(_ iso: Float, minISO: Float, maxISO: Float) -> Float {
        min(max(iso, minISO), maxISO)
    }

    /// Pure helper for tests: clamp exposure duration into a format’s legal range.
    static func clampExposureDuration(
        _ duration: CMTime,
        minDuration: CMTime,
        maxDuration: CMTime
    ) -> CMTime {
        if CMTimeCompare(duration, minDuration) < 0 { return minDuration }
        if CMTimeCompare(duration, maxDuration) > 0 { return maxDuration }
        return duration
    }

    // MARK: - Private

    private static func waitForAdjustmentsToSettle(
        _ device: AVCaptureDevice,
        timeout: TimeInterval
    ) {
        guard timeout > 0 else { return }
        let deadline = Date().addingTimeInterval(timeout)
        while Date() < deadline {
            if !device.isAdjustingExposure, !device.isAdjustingWhiteBalance, !device.isAdjustingFocus {
                return
            }
            Thread.sleep(forTimeInterval: 1.0 / 60.0)
        }
    }
}
