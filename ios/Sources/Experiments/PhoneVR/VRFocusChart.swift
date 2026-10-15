import Foundation
import simd

/// Line gratings the final pass draws straight onto the panel around each
/// lens axis during calibration. They skip the eye buffer, so whether their
/// 1-pixel lines look distinct depends only on the lenses, their focus, and
/// your eyes. The centre stays clear for the calibration target. Mirrors
/// `focus_chart` in the final-pass shader.
enum VRFocusChart {
    /// Clear radius around the lens axis, panel pixels.
    static let gap: Float = 20
    /// Side of each square patch, panel pixels.
    static let patch: Float = 36

    /// Farthest the chart reaches from the lens axis, panel pixels.
    static var extent: Float { gap + patch }

    /// Brightness (0 or 1) at an offset from the lens axis in panel pixels,
    /// y down, or nil where the scene shows through. Patches left and right of
    /// the centre hold vertical 1-pixel lines, patches above and below hold
    /// horizontal ones, and the corners hold 2-pixel lines.
    static func value(at d: SIMD2<Float>) -> Float? {
        let a = SIMD2(abs(d.x), abs(d.y))
        let bandX = a.x >= gap && a.x < gap + patch
        let bandY = a.y >= gap && a.y < gap + patch
        let cell = SIMD2(Int(floor(d.x)), Int(floor(d.y)))
        if bandX, a.y < patch / 2 {
            return Float(cell.x & 1)
        }
        if bandY, a.x < patch / 2 {
            return Float(cell.y & 1)
        }
        if bandX, bandY {
            let along = (d.x < 0) == (d.y < 0) ? cell.x : cell.y
            return Float((along >> 1) & 1)
        }
        return nil
    }

    /// The value the shader computes for drawable pixel (`x`, `y`), sampled
    /// at the pixel centre.
    static func value(atPixel x: Int, _ y: Int, lensCenter: SIMD2<Float>) -> Float? {
        value(at: SIMD2(Float(x) + 0.5, Float(y) + 0.5) - lensCenter)
    }
}
