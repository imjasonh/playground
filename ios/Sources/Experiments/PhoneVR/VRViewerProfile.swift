import Foundation

/// Half-angles of the lens field for the left eye, in degrees. The right eye
/// mirrors `outer` and `inner`.
struct VRFieldOfView: Codable, Equatable {
    var outer: Float
    var inner: Float
    var bottom: Float
    var top: Float

    var maximum: Float { max(outer, inner, bottom, top) }

    static func symmetric(_ degrees: Float) -> VRFieldOfView {
        VRFieldOfView(outer: degrees, inner: degrees, bottom: degrees, top: degrees)
    }
}

/// Lens viewer geometry. Field names and meanings match Cardboard's
/// `DeviceParams` so a Cardboard QR profile maps onto the same values.
/// `eyeRelief` and `lensFocalLength` are additions: Cardboard places the eye
/// at the lens, but 6DoF parallax needs the real eye position, and the focal
/// length sets the virtual image distance and lateral color.
struct VRViewerProfile: Codable, Equatable {
    enum VerticalAlignment: String, Codable, CaseIterable, Identifiable {
        case bottom
        case center
        case top

        var id: String { rawValue }
    }

    /// Screen to lens plane, meters.
    var screenToLensDistance: Float
    /// Lens centre to lens centre, meters.
    var interLensDistance: Float
    /// Eye to lens, meters.
    var eyeRelief: Float
    var verticalAlignment: VerticalAlignment
    /// Phone edge (the tray) to the lens axis, meters. Used for `bottom` and `top` alignment.
    var trayToLensDistance: Float
    var fieldOfView: VRFieldOfView
    /// Radial distortion `t = r (1 + k1 r² + k2 r⁴)` from screen tangent `r` to viewing tangent `t`.
    var distortionK1: Float
    var distortionK2: Float
    /// Lateral color: red and blue viewing angles relative to green.
    var redScale: Float
    var blueScale: Float
    /// Extra eye-buffer field on every side so timewarp has pixels to rotate in.
    var timewarpMarginDegrees: Float
    var lensFocalLength: Float

    /// The printed viewer: 42 mm from the lenses' optical center plane to the
    /// screen, 63.9 mm between lens centers, 24 mm eye relief, and lenses of
    /// 45 mm nominal focal length (43 to 45 mm per the manufacturer's
    /// drawing), with a ±27° round field. Distortion starts at Cardboard v1's
    /// coefficients; fit them on device.
    static let standard = VRViewerProfile(
        screenToLensDistance: 0.042,
        interLensDistance: 0.0639,
        eyeRelief: 0.024,
        verticalAlignment: .center,
        trayToLensDistance: 0.035,
        fieldOfView: .symmetric(27),
        distortionK1: 0.441,
        distortionK2: 0.156,
        redScale: 0.9952,
        blueScale: 1.0037,
        timewarpMarginDegrees: 2,
        lensFocalLength: 0.045
    )

    static let ranges = Ranges()

    struct Ranges {
        let screenToLensDistance: ClosedRange<Float> = 0.025...0.060
        let interLensDistance: ClosedRange<Float> = 0.050...0.080
        let eyeRelief: ClosedRange<Float> = 0.005...0.040
        let trayToLensDistance: ClosedRange<Float> = 0.015...0.060
        let fieldAngle: ClosedRange<Float> = 10...60
        let distortionK1: ClosedRange<Float> = -0.5...1.5
        let distortionK2: ClosedRange<Float> = -0.5...1.0
        let chromaticScale: ClosedRange<Float> = 0.97...1.03
        let timewarpMarginDegrees: ClosedRange<Float> = 0...6
        let lensFocalLength: ClosedRange<Float> = 0.030...0.080
    }

    var eyeToScreenDistance: Float { screenToLensDistance + eyeRelief }

    /// Distance from the eye to the lens's virtual image, meters, or nil when
    /// the screen sits at or beyond the focal length.
    var virtualImageDistance: Float? {
        let s = screenToLensDistance
        let f = lensFocalLength
        guard f > s else { return nil }
        return s * f / (f - s) + eyeRelief
    }

    func clamped() -> VRViewerProfile {
        let r = Self.ranges
        var p = self
        p.screenToLensDistance = p.screenToLensDistance.clamped(to: r.screenToLensDistance)
        p.interLensDistance = p.interLensDistance.clamped(to: r.interLensDistance)
        p.eyeRelief = p.eyeRelief.clamped(to: r.eyeRelief)
        p.trayToLensDistance = p.trayToLensDistance.clamped(to: r.trayToLensDistance)
        p.fieldOfView = VRFieldOfView(
            outer: p.fieldOfView.outer.clamped(to: r.fieldAngle),
            inner: p.fieldOfView.inner.clamped(to: r.fieldAngle),
            bottom: p.fieldOfView.bottom.clamped(to: r.fieldAngle),
            top: p.fieldOfView.top.clamped(to: r.fieldAngle)
        )
        p.distortionK1 = p.distortionK1.clamped(to: r.distortionK1)
        p.distortionK2 = p.distortionK2.clamped(to: r.distortionK2)
        p.redScale = p.redScale.clamped(to: r.chromaticScale)
        p.blueScale = p.blueScale.clamped(to: r.chromaticScale)
        p.timewarpMarginDegrees = p.timewarpMarginDegrees.clamped(to: r.timewarpMarginDegrees)
        p.lensFocalLength = p.lensFocalLength.clamped(to: r.lensFocalLength)
        return p
    }

    /// Paraxial lateral color of a thin acrylic (PMMA) magnifier. With the eye
    /// `eyeRelief` behind the lens, a screen point at height h is seen at
    /// `tan θ = h / (s + e - e s P)`, so the angle depends on the lens power P,
    /// which depends on wavelength. Returns red and blue angle scales relative
    /// to green (546 nm). A thin lens with the eye at the lens has no lateral color.
    static func estimatedChromaticScales(
        screenToLens s: Float,
        eyeRelief e: Float,
        focalLength f: Float
    ) -> (red: Float, blue: Float) {
        // PMMA refractive indices at 656 nm (C), 546 nm (e), and 486 nm (F).
        let nRed: Float = 1.4892
        let nGreen: Float = 1.4938
        let nBlue: Float = 1.4973
        let power = 1 / f
        func denominator(_ n: Float) -> Float {
            s + e - e * s * power * (n - 1) / (nGreen - 1)
        }
        let green = denominator(nGreen)
        return (red: green / denominator(nRed), blue: green / denominator(nBlue))
    }

    private enum CodingKeys: String, CodingKey {
        case screenToLensDistance, interLensDistance, eyeRelief, verticalAlignment
        case trayToLensDistance, fieldOfView, distortionK1, distortionK2
        case redScale, blueScale, timewarpMarginDegrees, lensFocalLength
    }

    init(
        screenToLensDistance: Float,
        interLensDistance: Float,
        eyeRelief: Float,
        verticalAlignment: VerticalAlignment,
        trayToLensDistance: Float,
        fieldOfView: VRFieldOfView,
        distortionK1: Float,
        distortionK2: Float,
        redScale: Float,
        blueScale: Float,
        timewarpMarginDegrees: Float,
        lensFocalLength: Float
    ) {
        self.screenToLensDistance = screenToLensDistance
        self.interLensDistance = interLensDistance
        self.eyeRelief = eyeRelief
        self.verticalAlignment = verticalAlignment
        self.trayToLensDistance = trayToLensDistance
        self.fieldOfView = fieldOfView
        self.distortionK1 = distortionK1
        self.distortionK2 = distortionK2
        self.redScale = redScale
        self.blueScale = blueScale
        self.timewarpMarginDegrees = timewarpMarginDegrees
        self.lensFocalLength = lensFocalLength
    }

    /// Missing keys fall back to `standard`, so profiles saved by older builds still load.
    init(from decoder: Decoder) throws {
        let c = try decoder.container(keyedBy: CodingKeys.self)
        let d = Self.standard
        screenToLensDistance = try c.decodeIfPresent(Float.self, forKey: .screenToLensDistance) ?? d.screenToLensDistance
        interLensDistance = try c.decodeIfPresent(Float.self, forKey: .interLensDistance) ?? d.interLensDistance
        eyeRelief = try c.decodeIfPresent(Float.self, forKey: .eyeRelief) ?? d.eyeRelief
        verticalAlignment = try c.decodeIfPresent(VerticalAlignment.self, forKey: .verticalAlignment) ?? d.verticalAlignment
        trayToLensDistance = try c.decodeIfPresent(Float.self, forKey: .trayToLensDistance) ?? d.trayToLensDistance
        fieldOfView = try c.decodeIfPresent(VRFieldOfView.self, forKey: .fieldOfView) ?? d.fieldOfView
        distortionK1 = try c.decodeIfPresent(Float.self, forKey: .distortionK1) ?? d.distortionK1
        distortionK2 = try c.decodeIfPresent(Float.self, forKey: .distortionK2) ?? d.distortionK2
        redScale = try c.decodeIfPresent(Float.self, forKey: .redScale) ?? d.redScale
        blueScale = try c.decodeIfPresent(Float.self, forKey: .blueScale) ?? d.blueScale
        timewarpMarginDegrees = try c.decodeIfPresent(Float.self, forKey: .timewarpMarginDegrees) ?? d.timewarpMarginDegrees
        lensFocalLength = try c.decodeIfPresent(Float.self, forKey: .lensFocalLength) ?? d.lensFocalLength
    }
}

extension Comparable {
    func clamped(to range: ClosedRange<Self>) -> Self {
        min(max(self, range.lowerBound), range.upperBound)
    }
}
