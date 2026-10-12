import Foundation

/// Metal Shading Language source for the renderer, compiled at runtime with
/// `MTLDevice.makeLibrary(source:options:)`. Runtime compilation keeps the
/// build independent of Xcode's optional Metal toolchain and lets the unit
/// tests compile every function and check struct layouts in the Simulator.
///
/// Struct layouts must match `VRShaderTypes.swift`. Defining `PVR_AMPLIFY=1`
/// builds the single-pass stereo variants that select the eye with
/// `[[amplification_id]]`; otherwise each eye is its own pass and reads its
/// index from buffer 4.
enum VRShaderSource {
    static let source = #"""
#include <metal_stdlib>
using namespace metal;

#if PVR_AMPLIFY
#define PVR_EYE_PARAM , ushort eye [[amplification_id]]
#define PVR_EYE eye
#else
#define PVR_EYE_PARAM , constant uint &eyeIndex [[buffer(4)]]
#define PVR_EYE eyeIndex
#endif

struct EyeUniforms {
    float4x4 viewProjection;
    float4x4 inverseViewProjection;
    float4 eyePosition;
    float4 maskEllipse;
};

struct FrameUniforms {
    float4 lightDirection;
    float4 skyZenith;
    float4 skyHorizon;
    float4 groundColor;
    float4 fog;
    float4 boundary;
    float4 gridMajor;
    float4 gridMinor;
};

struct InstanceUniforms {
    float4x4 model;
    float4 tint;
    float4 params;
};

struct PanelUniforms {
    float4x4 model;
    float4 tint;
    float4 params;
};

struct PassthroughUniforms {
    float4 corners[4];
    float4 tint;
};

struct DistortionEye {
    float3x3 rotation;
    float4 lensCenter;
    float4 fieldTangents;
    float4 bufferTangents;
    float4 params;
};

struct DistortionFrame {
    float4 coefficients;
    float4 chroma;
    float4 output;
};

struct SceneVertexIn {
    float3 position [[attribute(0)]];
    float3 normal [[attribute(1)]];
    float4 color [[attribute(2)]];
};

struct SceneVaryings {
    float4 position [[position]];
    float3 worldPosition;
    float3 normal;
    float4 color;
    float3 eyePosition;
};

struct SkyVaryings {
    float4 position [[position]];
    float3 direction;
};

struct QuadVaryings {
    float4 position [[position]];
    float2 uv;
};

struct MaskVaryings {
    float4 position [[position]];
};

static float3 srgb_to_linear(float3 c) {
    return select(pow((c + 0.055) / 1.055, float3(2.4)), c / 12.92, c <= 0.04045);
}

// Antialiased grid lines one cell apart in `coord`, `width` pixels wide, that
// fade out before the cells shrink below a pixel and start to shimmer.
static float grid_lines(float2 coord, float width) {
    float2 w = max(fwidth(coord), float2(1e-6));
    float2 g = abs(fract(coord - 0.5) - 0.5) / w;
    float d = min(g.x, g.y);
    float stroke = 1.0 - smoothstep(width * 0.5 - 0.5, width * 0.5 + 0.5, d);
    float lod = 1.0 - smoothstep(0.25, 0.6, max(w.x, w.y));
    return stroke * lod;
}

vertex SceneVaryings scene_vertex(SceneVertexIn in [[stage_in]],
                                  constant EyeUniforms *eyes [[buffer(1)]],
                                  constant InstanceUniforms &instance [[buffer(2)]]
                                  PVR_EYE_PARAM) {
    constant EyeUniforms &e = eyes[PVR_EYE];
    float4 world = instance.model * float4(in.position, 1.0);
    SceneVaryings out;
    out.position = e.viewProjection * world;
    out.worldPosition = world.xyz;
    out.normal = (instance.model * float4(in.normal, 0.0)).xyz;
    out.color = float4(srgb_to_linear(in.color.rgb), in.color.a) * instance.tint;
    out.eyePosition = e.eyePosition.xyz;
    return out;
}

static float3 apply_fog(float3 color, float3 p, float3 eye, constant FrameUniforms &frame) {
    float dist = distance(p, eye);
    float amount = 1.0 - exp(-max(dist - frame.fog.y, 0.0) * frame.fog.x);
    return mix(color, frame.skyHorizon.rgb * 0.55, amount);
}

fragment float4 scene_fragment(SceneVaryings in [[stage_in]],
                               constant InstanceUniforms &instance [[buffer(2)]],
                               constant FrameUniforms &frame [[buffer(3)]]) {
    int material = int(instance.params.x + 0.5);
    float3 n = normalize(in.normal);
    float3 base = in.color.rgb;
    float3 color;
    if (material == 1) {
        color = base * (1.0 + instance.params.y);
    } else if (material == 2) {
        float major = grid_lines(in.worldPosition.xz, 1.6);
        float minor = grid_lines(in.worldPosition.xz * 4.0, 1.0);
        float reach = distance(in.worldPosition.xz, in.eyePosition.xz);
        float fade = 1.0 - smoothstep(frame.fog.w * 0.5, frame.fog.w, reach);
        color = base;
        color = mix(color, frame.gridMinor.rgb, minor * frame.gridMinor.a * fade);
        color = mix(color, frame.gridMajor.rgb, major * frame.gridMajor.a * fade);
        float r = distance(in.worldPosition.xz, frame.boundary.xy);
        float ringWidth = 0.015 + fwidth(r);
        float ring = 1.0 - smoothstep(ringWidth * 0.5, ringWidth, abs(r - frame.boundary.z));
        color = mix(color, frame.gridMajor.rgb, ring * (0.35 + 0.65 * frame.boundary.w));
    } else if (material == 3) {
        float3 an = abs(n);
        float2 coord = an.x > 0.5 ? in.worldPosition.zy : (an.y > 0.5 ? in.worldPosition.xz : in.worldPosition.xy);
        float major = grid_lines(coord * 2.0, 1.8);
        float minor = grid_lines(coord * 10.0, 1.0);
        color = base;
        color = mix(color, frame.gridMinor.rgb, minor * frame.gridMinor.a);
        color = mix(color, frame.gridMajor.rgb, major);
        return float4(color, 1.0);
    } else {
        float3 l = frame.lightDirection.xyz;
        float diffuse = max(dot(n, l), 0.0);
        float hemisphere = 0.5 + 0.5 * n.y;
        float3 ambient = mix(frame.groundColor.rgb, frame.skyHorizon.rgb, hemisphere) * frame.lightDirection.w;
        color = base * (ambient + diffuse * float3(1.0, 0.94, 0.86));
    }
    return float4(apply_fog(color, in.worldPosition, in.eyePosition, frame), 1.0);
}

fragment float4 boundary_fragment(SceneVaryings in [[stage_in]],
                                  constant FrameUniforms &frame [[buffer(3)]]) {
    float2 offset = in.worldPosition.xz - frame.boundary.xy;
    float around = atan2(offset.y, offset.x) * frame.boundary.z;
    float lines = grid_lines(float2(around, in.worldPosition.y) * 4.0, 1.5);
    float alpha = frame.boundary.w * (0.12 + 0.88 * lines);
    return float4(frame.gridMajor.rgb * alpha, alpha);
}

vertex SkyVaryings sky_vertex(uint vid [[vertex_id]],
                              constant EyeUniforms *eyes [[buffer(1)]]
                              PVR_EYE_PARAM) {
    float2 ndc = float2(vid == 1 ? 3.0 : -1.0, vid == 2 ? 3.0 : -1.0);
    SkyVaryings out;
    out.position = float4(ndc, 0.0, 1.0);
    out.direction = (eyes[PVR_EYE].inverseViewProjection * float4(ndc, 0.0, 1.0)).xyz;
    return out;
}

fragment float4 sky_fragment(SkyVaryings in [[stage_in]],
                             constant FrameUniforms &frame [[buffer(3)]]) {
    float3 d = normalize(in.direction);
    float3 color;
    if (d.y >= 0.0) {
        float t = pow(1.0 - d.y, 4.0);
        color = mix(frame.skyZenith.rgb, frame.skyHorizon.rgb, t);
    } else {
        float t = pow(1.0 + d.y, 8.0);
        color = mix(frame.groundColor.rgb, frame.skyHorizon.rgb * 0.5, t);
    }
    float glow = pow(max(dot(d, frame.lightDirection.xyz), 0.0), 24.0);
    return float4(color + frame.skyHorizon.rgb * glow * 0.25, 1.0);
}

vertex MaskVaryings mask_vertex(uint vid [[vertex_id]],
                                constant float4 *directions [[buffer(0)]],
                                constant EyeUniforms *eyes [[buffer(1)]]
                                PVR_EYE_PARAM) {
    float4 v = directions[vid];
    float4 ellipse = eyes[PVR_EYE].maskEllipse;
    float2 inner = ellipse.xy + v.xy * ellipse.zw;
    float2 dir = normalize(inner - ellipse.xy);
    float2 safe = select(dir, float2(1e-6), abs(dir) < 1e-6);
    float2 bounds = (sign(safe) * 1.01 - ellipse.xy) / safe;
    float toEdge = min(bounds.x, bounds.y);
    float toInner = length(inner - ellipse.xy);
    float2 p = ellipse.xy + dir * (v.z > 0.5 ? toEdge : min(toInner, toEdge));
    MaskVaryings out;
    out.position = float4(p, 1.0, 1.0);
    return out;
}

fragment float4 mask_fragment(MaskVaryings in [[stage_in]]) {
    return float4(0.0);
}

vertex QuadVaryings panel_vertex(uint vid [[vertex_id]],
                                 constant EyeUniforms *eyes [[buffer(1)]],
                                 constant PanelUniforms &panel [[buffer(2)]]
                                 PVR_EYE_PARAM) {
    float2 corner = float2(float(vid & 1u), float(vid >> 1u));
    float4 local = float4(corner.x - 0.5, 0.5 - corner.y, 0.0, 1.0);
    QuadVaryings out;
    out.position = eyes[PVR_EYE].viewProjection * (panel.model * local);
    out.uv = corner;
    return out;
}

fragment float4 panel_fragment(QuadVaryings in [[stage_in]],
                               texture2d<float> image [[texture(0)]],
                               constant PanelUniforms &panel [[buffer(2)]]) {
    constexpr sampler s(address::clamp_to_edge, filter::linear, mip_filter::linear);
    return image.sample(s, in.uv) * panel.tint.a;
}

// Gaze reticle: a ring with a centre dot, plus an outer arc that fills
// clockwise from the top as a dwell selection completes (params.x).
fragment float4 reticle_fragment(QuadVaryings in [[stage_in]],
                                 constant PanelUniforms &panel [[buffer(2)]]) {
    float2 p = in.uv * 2.0 - 1.0;
    float d = length(p);
    float aa = max(fwidth(d), 1e-4);
    float ring = 1.0 - smoothstep(0.07 - aa, 0.07 + aa, abs(d - 0.45));
    float dotMask = 1.0 - smoothstep(0.12 - aa, 0.12 + aa, d);
    float fraction = fract(atan2(p.x, p.y) / (2.0 * M_PI_F) + 1.0);
    float arcBand = 1.0 - smoothstep(0.08 - aa, 0.08 + aa, abs(d - 0.8));
    float arc = (panel.params.x > 0.0 && fraction <= panel.params.x) ? arcBand : 0.0;
    float highlight = panel.params.y;
    float alpha = max(max(ring * (0.7 + 0.3 * highlight), dotMask * (0.5 + 0.5 * highlight)), arc);
    return float4(panel.tint.rgb * alpha, alpha) * panel.tint.a;
}

vertex QuadVaryings passthrough_vertex(uint vid [[vertex_id]],
                                       constant EyeUniforms *eyes [[buffer(1)]],
                                       constant PassthroughUniforms &camera [[buffer(2)]]
                                       PVR_EYE_PARAM) {
    QuadVaryings out;
    out.position = eyes[PVR_EYE].viewProjection * float4(camera.corners[vid].xyz, 1.0);
    out.uv = float2(float(vid & 1u), float(vid >> 1u));
    return out;
}

fragment float4 passthrough_fragment(QuadVaryings in [[stage_in]],
                                     texture2d<float> luma [[texture(0)]],
                                     texture2d<float> chroma [[texture(1)]],
                                     constant PassthroughUniforms &camera [[buffer(2)]]) {
    constexpr sampler s(address::clamp_to_edge, filter::linear);
    // Full-range BT.601 YCbCr, as ARKit captures it.
    const float4x4 ycbcrToRGB = float4x4(float4(+1.0000f, +1.0000f, +1.0000f, +0.0000f),
                                         float4(+0.0000f, -0.3441f, +1.7720f, +0.0000f),
                                         float4(+1.4020f, -0.7141f, +0.0000f, +0.0000f),
                                         float4(-0.7010f, +0.5291f, -0.8860f, +1.0000f));
    float4 ycbcr = float4(luma.sample(s, in.uv).r, chroma.sample(s, in.uv).rg, 1.0);
    float3 rgb = srgb_to_linear(saturate((ycbcrToRGB * ycbcr).rgb));
    return float4(rgb * camera.tint.a, camera.tint.a);
}

vertex MaskVaryings final_vertex(uint vid [[vertex_id]],
                                 constant float2 *pixels [[buffer(0)]],
                                 constant DistortionFrame &frame [[buffer(1)]]) {
    float2 p = pixels[vid];
    MaskVaryings out;
    out.position = float4(p.x / frame.output.z * 2.0 - 1.0, 1.0 - p.y / frame.output.w * 2.0, 0.0, 1.0);
    return out;
}

static float4 sample_eye(texture2d_array<float> image, sampler s, float2 t, constant DistortionEye &eye, uint layer) {
    float3 d = eye.rotation * float3(t, -1.0);
    if (d.z > -1e-4) {
        return float4(0.0);
    }
    float2 rendered = d.xy / -d.z;
    float4 b = eye.bufferTangents;
    float2 uv = float2((rendered.x - b.x) / (b.y - b.x), (b.w - rendered.y) / (b.w - b.z));
    return image.sample(s, uv, layer);
}

// Lens correction, lateral color, and rotational timewarp in one pass. Each
// panel pixel is mapped to the viewing angle the lens shows it at; each color
// channel is scaled by its own magnification; the direction is rotated from
// the late-latched head orientation back into the orientation the eye buffer
// was rendered with; and the eye buffer is sampled there.
fragment float4 final_fragment(MaskVaryings in [[stage_in]],
                               texture2d_array<float> image [[texture(0)]],
                               constant DistortionFrame &frame [[buffer(1)]],
                               constant DistortionEye &eye [[buffer(2)]]) {
    constexpr sampler s(address::clamp_to_zero, filter::linear);
    float2 r = (in.position.xy - eye.lensCenter.xy) * float2(1.0, -1.0) / eye.lensCenter.z;
    float r2 = dot(r, r);
    float2 t = r * (1.0 + r2 * (frame.coefficients.x + r2 * frame.coefficients.y));
    float radius = length(t);
    float fieldRadius = eye.lensCenter.w * eye.params.y;
    float feather = frame.output.y;
    float edge = 1.0 - smoothstep(fieldRadius - feather, fieldRadius, radius);
    float4 f = eye.fieldTangents;
    edge *= step(f.x, t.x) * step(t.x, f.y) * step(f.z, t.y) * step(t.y, f.w);
    if (edge <= 0.0) {
        return float4(0.0, 0.0, 0.0, 1.0);
    }
    uint layer = uint(eye.params.x + 0.5);
    float3 scales = frame.chroma.w > 0.5 ? frame.chroma.xyz : float3(1.0);
    float3 rgb = float3(sample_eye(image, s, t * scales.x, eye, layer).r,
                        sample_eye(image, s, t * scales.y, eye, layer).g,
                        sample_eye(image, s, t * scales.z, eye, layer).b);
    return float4(rgb * edge * frame.output.x, 1.0);
}
"""#
}
