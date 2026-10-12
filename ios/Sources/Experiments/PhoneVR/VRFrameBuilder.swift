import Foundation
import simd

struct VRDrawInstance {
    var mesh: VRMeshKind
    var uniforms: VRInstanceUniforms
}

/// Builds shader uniforms from poses, the lens layout, and the scene.
enum VRFrameBuilder {
    /// Dusk palette, linear RGB.
    static let skyZenith = SIMD4<Float>(0.010, 0.022, 0.060, 1)
    static let skyHorizon = SIMD4<Float>(0.82, 0.42, 0.22, 1)
    static let ground = SIMD4<Float>(0.006, 0.008, 0.012, 1)
    static let lightDirection = simd_normalize(SIMD3<Float>(-0.45, 0.8, 0.4))
    static let gridMajor = SIMD4<Float>(0.08, 0.64, 0.58, 0.9)
    static let gridMinor = SIMD4<Float>(0.03, 0.2, 0.2, 0.6)

    /// Pose of each eye in the scene for a head pose in the scene.
    static func eyePoses(layout: VRStereoLayout, sceneFromHead: VRPose) -> [VRPose] {
        VREye.allCases.map { eye in
            sceneFromHead * VRPose(rotation: VRMath.identityRotation, position: layout[eye].eyeInScreen)
        }
    }

    static func eyeUniforms(layout: VRStereoLayout, sceneFromHead: VRPose) -> [VREyeUniforms] {
        let poses = eyePoses(layout: layout, sceneFromHead: sceneFromHead)
        return VREye.allCases.map { eye in
            let pose = poses[eye.rawValue]
            let viewProjection = layout.projection(for: eye) * pose.inverse.matrix
            return VREyeUniforms(
                viewProjection: viewProjection,
                inverseViewProjection: viewProjection.inverse,
                eyePosition: SIMD4(pose.position, 1),
                maskEllipse: layout.maskEllipse(for: eye)
            )
        }
    }

    static func frameUniforms(boundaryCenter: SIMD3<Float>, boundaryRadius: Float, boundaryVisibility: Float) -> VRFrameUniforms {
        VRFrameUniforms(
            lightDirection: SIMD4(lightDirection, 0.55),
            skyZenith: skyZenith,
            skyHorizon: skyHorizon,
            groundColor: ground,
            fog: SIMD4(0.035, 6, 0, 25),
            boundary: SIMD4(boundaryCenter.x, boundaryCenter.z, boundaryRadius, boundaryVisibility),
            gridMajor: gridMajor,
            gridMinor: gridMinor
        )
    }

    /// Meshes are white, so the object's color arrives as the tint.
    static func instance(_ object: VRSceneObject, time: Double, tint: SIMD4<Float> = SIMD4(repeating: 1)) -> VRDrawInstance {
        VRDrawInstance(
            mesh: object.mesh,
            uniforms: VRInstanceUniforms(
                model: object.modelMatrix(at: time),
                tint: VRPalette.linear(object.color) * tint,
                params: SIMD4(Float(object.material.rawValue), object.glow, 0, 0)
            )
        )
    }

    /// Scene objects to draw. Passthrough hides the floor and the room so the
    /// camera image shows through.
    static func instances(scene: VRSceneKind, reduced: Bool, time: Double, passthrough: Bool) -> [VRDrawInstance] {
        VRSceneLayout.objects(for: scene, reduced: reduced)
            .filter { !(passthrough && ($0.material == .floorGrid || $0.material == .roomGrid)) }
            .map { instance($0, time: time) }
    }

    /// The menu hub ring on the floor, brighter while gazed at.
    static func hubInstance(center: SIMD3<Float>, highlighted: Bool, time: Double) -> VRDrawInstance {
        let pulse = Float(0.5 + 0.5 * sin(time * 2.5))
        let object = VRSceneObject(
            mesh: .disc, material: .emissive, position: center,
            scale: SIMD3(VRExperience.hubRadius, 1, VRExperience.hubRadius),
            color: VRPalette.teal, glow: highlighted ? 1.2 : 0.2 + 0.3 * pulse
        )
        let alpha: Float = highlighted ? 1 : 0.55
        return instance(object, time: 0, tint: SIMD4(alpha, alpha, alpha, 1))
    }

    /// A thin emissive beam from `origin` along `direction` for the controller pointer.
    static func pointerInstance(origin: SIMD3<Float>, direction: SIMD3<Float>, length: Float) -> VRDrawInstance {
        let rotation = simd_quatf(from: SIMD3(0, 1, 0), to: simd_normalize(direction))
        let model = VRPose(rotation: rotation, position: origin).matrix * VRMath.scale(SIMD3(0.003, length, 0.003))
        return VRDrawInstance(
            mesh: .cylinder,
            uniforms: VRInstanceUniforms(
                model: model,
                tint: SIMD4(repeating: 1),
                params: SIMD4(Float(VRMaterial.emissive.rawValue), 1.5, 0, 0)
            )
        )
    }

    static func boundaryUniforms(center: SIMD3<Float>, radius: Float) -> VRInstanceUniforms {
        VRInstanceUniforms(
            model: VRMath.translation(center) * VRMath.scale(SIMD3(radius, 2.6, radius)),
            tint: SIMD4(repeating: 1),
            params: SIMD4(Float(VRMaterial.boundary.rawValue), 0, 0, 0)
        )
    }

    static func panelUniforms(_ placement: VRPanelPlacement, opacity: Float) -> VRPanelUniforms {
        VRPanelUniforms(model: placement.modelMatrix, tint: SIMD4(1, 1, 1, opacity), params: .zero)
    }

    /// A panel that rides along with the head at an offset in head coordinates.
    static func headLocked(head: VRPose, offset: SIMD3<Float>, size: SIMD2<Float>) -> VRPanelPlacement {
        let center = head.transformPoint(offset)
        let tilt = -atan2(offset.y, -offset.z)
        return VRPanelPlacement(center: center, rotation: (head.rotation * VRMath.rotationX(tilt)).normalized, size: size)
    }

    /// Gaze reticle `distance` meters along the ray, facing the eye, about
    /// 1.6° across wherever it sits.
    static func reticleUniforms(head: VRPose, origin: SIMD3<Float>, direction: SIMD3<Float>, distance: Float, progress: Float, highlighted: Bool) -> VRPanelUniforms {
        let center = origin + simd_normalize(direction) * distance
        let size = 2 * simd_distance(center, head.position) * tan(VRMath.radians(0.8))
        let model = VRPose(rotation: head.rotation, position: center).matrix * VRMath.scale(SIMD3(size, size, 1))
        return VRPanelUniforms(
            model: model,
            tint: SIMD4(0.92, 0.98, 1, 1),
            params: SIMD4(progress, highlighted ? 1 : 0, 0, 0)
        )
    }

    /// Camera image corners at `distance` meters in front of the camera at
    /// its capture pose. Placing the image where it was taken lets head
    /// motion and timewarp keep it fixed in the world; the scale is right
    /// only at that distance.
    static func passthroughUniforms(
        sceneFromCamera: VRPose,
        intrinsics: simd_float3x3,
        imageWidth: Float,
        imageHeight: Float,
        distance: Float,
        opacity: Float
    ) -> VRPassthroughUniforms {
        let fx = intrinsics[0][0]
        let fy = intrinsics[1][1]
        let cx = intrinsics[2][0]
        let cy = intrinsics[2][1]
        func corner(_ u: Float, _ v: Float) -> SIMD4<Float> {
            let inCamera = SIMD3((u - cx) / fx, -(v - cy) / fy, -1) * distance
            return SIMD4(sceneFromCamera.transformPoint(inCamera), 1)
        }
        return VRPassthroughUniforms(
            corner0: corner(0, 0),
            corner1: corner(imageWidth, 0),
            corner2: corner(0, imageHeight),
            corner3: corner(imageWidth, imageHeight),
            tint: SIMD4(1, 1, 1, opacity)
        )
    }

    /// Final-pass values shared by both eyes.
    static func distortionFrame(layout: VRStereoLayout, chromaticCorrection: Bool, brightness: Float) -> VRDistortionFrameUniforms {
        let p = layout.profile
        return VRDistortionFrameUniforms(
            coefficients: SIMD4(p.distortionK1, p.distortionK2, 0, 0),
            chroma: SIMD4(p.redScale, 1, p.blueScale, chromaticCorrection ? 1 : 0),
            output: SIMD4(brightness, 0.006, Float(layout.screen.widthPixels), Float(layout.screen.heightPixels))
        )
    }

    /// Final-pass values per eye. `timewarp` rotates directions from the
    /// late-latched head orientation into the one the eye buffer used.
    static func distortionEyes(layout: VRStereoLayout, timewarp: simd_quatf, vignette: Float) -> [VRDistortionEyeUniforms] {
        let rotation = simd_float3x3(timewarp.normalized)
        return VREye.allCases.map { eye in
            let e = layout[eye]
            return VRDistortionEyeUniforms(
                rotation: rotation,
                lensCenter: SIMD4(e.lensCenterPixels.x, e.lensCenterPixels.y, layout.pixelsPerTangent, e.fieldRadiusTangent),
                fieldTangents: e.fieldTangents.shaderVector,
                bufferTangents: e.bufferTangents.shaderVector,
                params: SIMD4(Float(eye.rawValue), vignette, 0, 0)
            )
        }
    }

    /// Rotation for the final pass: from the late head orientation into the
    /// rendered one. Both orientations are world-from-head.
    static func timewarpRotation(rendered: simd_quatf, late: simd_quatf) -> simd_quatf {
        (rendered.inverse * late).normalized
    }

    /// Where the eye buffer is sampled for a viewing tangent after timewarp.
    /// Mirrors `sample_eye` in the shader; returns nil behind the eye.
    static func timewarpedUV(tangent t: SIMD2<Float>, rotation: simd_quatf, buffer: VRTangents) -> SIMD2<Float>? {
        let d = rotation.act(SIMD3(t.x, t.y, -1))
        guard d.z < -1e-4 else { return nil }
        return buffer.uv(fromTangent: SIMD2(d.x, d.y) / -d.z)
    }
}
