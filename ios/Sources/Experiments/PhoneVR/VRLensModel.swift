import Foundation
import simd

/// Polynomial radial distortion of a magnifier lens. A point `r` screen
/// tangents from the lens axis (screen distance over screen-to-lens distance)
/// is seen at viewing tangent `t = r (1 + k1 r² + k2 r⁴)`.
struct VRRadialDistortion: Equatable {
    var k1: Float
    var k2: Float

    /// Screen radius past which `distort` stops increasing, capped at 3.
    var monotonicLimit: Float {
        var r: Float = 0
        while r < 3 {
            if slope(r + 0.01) <= 0 { return r }
            r += 0.01
        }
        return 3
    }

    func distort(_ r: Float) -> Float {
        let r2 = r * r
        return r * (1 + r2 * (k1 + r2 * k2))
    }

    func slope(_ r: Float) -> Float {
        let r2 = r * r
        return 1 + r2 * (3 * k1 + 5 * k2 * r2)
    }

    func distort(_ p: SIMD2<Float>) -> SIMD2<Float> {
        let r2 = simd_length_squared(p)
        return p * (1 + r2 * (k1 + r2 * k2))
    }

    /// Screen radius whose viewing tangent is `t`. Newton's method, with a
    /// bisection fallback when the polynomial isn't monotonic near the answer.
    func undistort(_ t: Float) -> Float {
        guard t > 0 else { return 0 }
        let limit = monotonicLimit
        var r = min(t, limit)
        for _ in 0..<12 {
            let s = slope(r)
            guard s > 1e-4 else { break }
            let next = r - (distort(r) - t) / s
            guard next.isFinite, next >= 0, next <= limit else { break }
            if abs(next - r) < 1e-7 {
                r = next
                break
            }
            r = next
        }
        if abs(distort(r) - t) < 1e-5 { return r }
        var lo: Float = 0
        var hi = limit
        guard distort(hi) >= t else { return hi }
        for _ in 0..<60 {
            let mid = (lo + hi) / 2
            if distort(mid) < t { lo = mid } else { hi = mid }
        }
        return (lo + hi) / 2
    }

    func undistort(_ p: SIMD2<Float>) -> SIMD2<Float> {
        let t = simd_length(p)
        guard t > 0 else { return p }
        return p * (undistort(t) / t)
    }
}

enum VREye: Int, CaseIterable, Identifiable {
    case left = 0
    case right = 1

    var id: Int { rawValue }
    /// -1 for the left eye, +1 for the right.
    var sign: Float { self == .left ? -1 : 1 }
}

/// Where each eye's image lands on the panel and the frustum it renders.
struct VRStereoLayout {
    struct EyeLayout {
        var eye: VREye
        /// Lens axis on the panel, drawable pixels with y down.
        var lensCenterPixels: SIMD2<Float>
        /// Eye position in the screen frame, meters.
        var eyeInScreen: SIMD3<Float>
        /// Viewing tangents the lens shows on each side, after the panel edges clip them.
        var fieldTangents: VRTangents
        /// Eye-buffer frustum: the field plus the timewarp margin.
        var bufferTangents: VRTangents
        /// Radius of the round lens field in viewing tangents.
        var fieldRadiusTangent: Float
        /// That round field's radius on the panel, pixels.
        var visibleRadiusPixels: Float
        /// Radius of the eye-buffer region the final pass can sample, in tangents.
        var maskRadiusTangent: Float
    }

    /// Gap between the phone's edge and its panel, which Cardboard assumes is 3 mm.
    static let trayBorder: Float = 0.003
    static let nearPlane: Float = 0.05

    let screen: VRPhoneScreen
    let profile: VRViewerProfile
    let distortion: VRRadialDistortion
    /// Panel pixels per screen tangent: screen-to-lens distance times pixel density.
    let pixelsPerTangent: Float
    let eyes: [EyeLayout]

    init(screen: VRPhoneScreen, profile rawProfile: VRViewerProfile) {
        let profile = rawProfile.clamped()
        self.screen = screen
        self.profile = profile
        let distortion = VRRadialDistortion(k1: profile.distortionK1, k2: profile.distortionK2)
        self.distortion = distortion
        let ppm = screen.pixelsPerMeter
        let pixelsPerTangent = profile.screenToLensDistance * ppm
        self.pixelsPerTangent = pixelsPerTangent

        let screenWidth = screen.widthMeters
        let screenHeight = screen.heightMeters
        let lensFromBottom: Float
        switch profile.verticalAlignment {
        case .center:
            lensFromBottom = screenHeight / 2
        case .bottom:
            lensFromBottom = profile.trayToLensDistance - Self.trayBorder
        case .top:
            lensFromBottom = screenHeight - profile.trayToLensDistance + Self.trayBorder
        }
        let lensY = lensFromBottom - screenHeight / 2
        let halfLens = profile.interLensDistance / 2
        let channelMax = max(1, profile.redScale, profile.blueScale)
        let margin = profile.timewarpMarginDegrees

        func fieldAngle(screenDistance: Float, limitDegrees: Float) -> Float {
            let screenTangent = max(0, screenDistance) / profile.screenToLensDistance
            let reachable = VRMath.degrees(atan(distortion.distort(min(screenTangent, distortion.monotonicLimit))))
            return min(limitDegrees, reachable)
        }

        var eyes: [EyeLayout] = []
        for eye in VREye.allCases {
            let lensX = eye.sign * halfLens
            let outerDistance = screenWidth / 2 - halfLens
            let innerDistance = halfLens
            let fov = profile.fieldOfView
            let outer = fieldAngle(screenDistance: outerDistance, limitDegrees: fov.outer)
            let inner = fieldAngle(screenDistance: innerDistance, limitDegrees: fov.inner)
            let bottom = fieldAngle(screenDistance: lensFromBottom, limitDegrees: fov.bottom)
            let top = fieldAngle(screenDistance: screenHeight - lensFromBottom, limitDegrees: fov.top)
            let leftAngle = eye == .left ? outer : inner
            let rightAngle = eye == .left ? inner : outer
            let field = VRTangents(
                left: -tan(VRMath.radians(leftAngle)),
                right: tan(VRMath.radians(rightAngle)),
                bottom: -tan(VRMath.radians(bottom)),
                top: tan(VRMath.radians(top))
            )
            let radiusTangent = tan(VRMath.radians(fov.maximum))
            let maskAngle = atan(radiusTangent * channelMax) + VRMath.radians(margin)
            let lensCenter = SIMD2<Float>(
                screen.centerPixels.x + lensX * ppm,
                screen.centerPixels.y - lensY * ppm
            )
            eyes.append(EyeLayout(
                eye: eye,
                lensCenterPixels: lensCenter,
                eyeInScreen: SIMD3(lensX, lensY, profile.eyeToScreenDistance),
                fieldTangents: field,
                bufferTangents: field.expanded(byDegrees: margin),
                fieldRadiusTangent: radiusTangent,
                visibleRadiusPixels: distortion.undistort(radiusTangent) * pixelsPerTangent,
                maskRadiusTangent: tan(min(maskAngle, VRMath.radians(85)))
            ))
        }
        self.eyes = eyes
    }

    subscript(eye: VREye) -> EyeLayout { eyes[eye.rawValue] }

    func projection(for eye: VREye, near: Float = VRStereoLayout.nearPlane) -> simd_float4x4 {
        VRMath.perspective(self[eye].bufferTangents, near: near)
    }

    /// Eye-buffer pixel size when `resolution` pixels span the wider tangent range.
    func eyeBufferSize(resolution: Int) -> (width: Int, height: Int) {
        let t = self[.left].bufferTangents
        if t.width >= t.height {
            return (resolution, max(1, Int((Float(resolution) * t.height / t.width).rounded())))
        }
        return (max(1, Int((Float(resolution) * t.width / t.height).rounded())), resolution)
    }

    /// Panel pixels per degree at the lens axis, where distortion has unit slope.
    var displayPixelsPerDegree: Float { pixelsPerTangent * .pi / 180 }

    /// Eye-buffer pixels per degree at the lens axis.
    func eyeBufferPixelsPerDegree(resolution: Int) -> Float {
        let size = eyeBufferSize(resolution: resolution)
        return Float(size.width) / self[.left].bufferTangents.width * .pi / 180
    }

    /// Eye-buffer pixels per panel pixel at the lens axis, where the panel is
    /// sharpest through the lens.
    func centerSampling(resolution: Int) -> Float {
        eyeBufferPixelsPerDegree(resolution: resolution) / displayPixelsPerDegree
    }

    /// How far each lens axis sits inboard of the centre of its half of the panel, pixels.
    var lensInboardOffsetPixels: Float {
        Float(screen.widthPixels) / 4 - profile.interLensDistance / 2 * screen.pixelsPerMeter
    }

    /// Hidden-area mask in eye-buffer NDC: ellipse centre (x, y) and radii (z, w).
    func maskEllipse(for eye: VREye) -> SIMD4<Float> {
        let layout = self[eye]
        let t = layout.bufferTangents
        let center = t.ndc(fromTangent: .zero)
        return SIMD4(center.x, center.y, 2 * layout.maskRadiusTangent / t.width, 2 * layout.maskRadiusTangent / t.height)
    }

    /// Share of eye-buffer pixels the hidden-area mask removes.
    func hiddenAreaFraction(for eye: VREye, samples: Int = 128) -> Float {
        let layout = self[eye]
        let t = layout.bufferTangents
        let r2 = layout.maskRadiusTangent * layout.maskRadiusTangent
        var outside = 0
        for j in 0..<samples {
            for i in 0..<samples {
                let uv = SIMD2((Float(i) + 0.5) / Float(samples), (Float(j) + 0.5) / Float(samples))
                if simd_length_squared(t.tangent(fromUV: uv)) > r2 { outside += 1 }
            }
        }
        return Float(outside) / Float(samples * samples)
    }

    /// Viewing tangent for a drawable pixel seen through `eye`'s lens, or nil
    /// when the pixel is outside that eye's field. Mirrors the final-pass shader.
    func viewingTangent(forPixel pixel: SIMD2<Float>, eye: VREye) -> SIMD2<Float>? {
        let layout = self[eye]
        let screenTangent = (pixel - layout.lensCenterPixels) * SIMD2(1, -1) / pixelsPerTangent
        let t = distortion.distort(screenTangent)
        guard simd_length(t) <= layout.fieldRadiusTangent, layout.fieldTangents.contains(t) else { return nil }
        return t
    }

    /// Drawable pixel that shows viewing tangent `t` through `eye`'s lens.
    func pixel(forViewingTangent t: SIMD2<Float>, eye: VREye) -> SIMD2<Float> {
        let layout = self[eye]
        let screenTangent = distortion.undistort(t)
        return layout.lensCenterPixels + screenTangent * SIMD2(1, -1) * pixelsPerTangent
    }
}

/// Numbers from the engineering sketch's "viewer in numbers" table, computed
/// for the current panel and profile.
struct VRViewerReport: Equatable {
    var panelWidthMillimeters: Float
    var panelHeightMillimeters: Float
    var halfWidthPixels: Int
    var lensInboardMillimeters: Float
    var lensInboardPixels: Float
    var fieldDiameterMillimeters: Float
    var fieldDiameterPixels: Float
    var displayPixelsPerDegree: Float
    var virtualImageMeters: Float?
    var eyeToScreenMillimeters: Float

    init(layout: VRStereoLayout) {
        let screen = layout.screen
        let profile = layout.profile
        panelWidthMillimeters = screen.widthMeters * 1000
        panelHeightMillimeters = screen.heightMeters * 1000
        halfWidthPixels = screen.widthPixels / 2
        lensInboardPixels = layout.lensInboardOffsetPixels
        lensInboardMillimeters = lensInboardPixels / screen.pixelsPerMeter * 1000
        fieldDiameterPixels = layout[.left].visibleRadiusPixels * 2
        fieldDiameterMillimeters = fieldDiameterPixels / screen.pixelsPerMeter * 1000
        displayPixelsPerDegree = layout.displayPixelsPerDegree
        virtualImageMeters = profile.virtualImageDistance
        eyeToScreenMillimeters = profile.eyeToScreenDistance * 1000
    }
}
