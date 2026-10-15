import Foundation
import simd

// Swift mirrors of the structs in `VRShaderSource`. Only simd types with
// fixed sizes and alignment appear here so the layouts match Metal's; the
// renderer tests compare sizes against Metal's reflection data.

/// Per-eye camera data. 160 bytes.
struct VREyeUniforms {
    var viewProjection: simd_float4x4
    var inverseViewProjection: simd_float4x4
    /// Scene-space eye position; w is unused.
    var eyePosition: SIMD4<Float>
    /// Hidden-area mask ellipse in NDC: centre (x, y) and radii (z, w).
    var maskEllipse: SIMD4<Float>
}

/// Lighting, sky, fog, and play-area values shared by every draw. 128 bytes.
struct VRFrameUniforms {
    /// Unit direction toward the light; w is the ambient strength.
    var lightDirection: SIMD4<Float>
    var skyZenith: SIMD4<Float>
    var skyHorizon: SIMD4<Float>
    var groundColor: SIMD4<Float>
    /// x fog density per meter, y fog start distance, z unused, w grid fade distance.
    var fog: SIMD4<Float>
    /// Play-area centre (x, y = scene x, z), radius (z), wall visibility (w).
    var boundary: SIMD4<Float>
    /// Linear color in xyz, strength in w.
    var gridMajor: SIMD4<Float>
    var gridMinor: SIMD4<Float>
}

/// One scene object. 96 bytes.
struct VRInstanceUniforms {
    var model: simd_float4x4
    /// Linear color multiplier; a is opacity.
    var tint: SIMD4<Float>
    /// x material (`VRMaterial`), y glow.
    var params: SIMD4<Float>
}

/// A textured panel or the reticle. 96 bytes.
struct VRPanelUniforms {
    var model: simd_float4x4
    /// Linear tint; a is opacity.
    var tint: SIMD4<Float>
    /// Reticle: x dwell progress, y highlight.
    var params: SIMD4<Float>
}

/// Camera image quad: scene-space corners (top left, top right, bottom left,
/// bottom right) and opacity in `tint.w`. 80 bytes.
struct VRPassthroughUniforms {
    var corner0: SIMD4<Float>
    var corner1: SIMD4<Float>
    var corner2: SIMD4<Float>
    var corner3: SIMD4<Float>
    var tint: SIMD4<Float>
}

/// Final pass, per eye. 112 bytes.
struct VRDistortionEyeUniforms {
    /// Maps directions in the late-latched eye frame into the eye frame the eye buffer was rendered with.
    var rotation: simd_float3x3
    /// Lens axis in drawable pixels (x, y), pixels per screen tangent (z), round-field radius in tangents (w).
    var lensCenter: SIMD4<Float>
    /// Viewing-tangent limits: left, right, bottom, top.
    var fieldTangents: SIMD4<Float>
    /// Eye-buffer frustum tangents: left, right, bottom, top.
    var bufferTangents: SIMD4<Float>
    /// x eye-buffer layer, y field radius scale for the comfort vignette.
    var params: SIMD4<Float>
}

/// Final pass, shared. 64 bytes.
struct VRDistortionFrameUniforms {
    /// k1, k2.
    var coefficients: SIMD4<Float>
    /// Red, green, and blue angle scales; w > 0.5 enables them.
    var chroma: SIMD4<Float>
    /// x brightness (0 black to 1), y edge feather in tangents, z and w drawable size in pixels.
    var output: SIMD4<Float>
    /// x > 0.5 samples the eye buffer with Catmull-Rom instead of bilinear
    /// filtering; y > 0.5 draws `VRFocusChart` around each lens axis.
    var options: SIMD4<Float>
}

extension VRTangents {
    /// Left, right, bottom, top, as the shaders expect.
    var shaderVector: SIMD4<Float> { SIMD4(left, right, bottom, top) }
}
