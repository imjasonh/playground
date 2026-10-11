import Foundation
import simd

/// Places the scene in the ARKit world and keeps the physical play area.
///
/// Scene coordinates put the floor at y = 0 and the wearer's recentered
/// heading along -Z. Recentering, snap turns, and stick locomotion move the
/// scene; the play-area boundary stays fixed to the room, because it exists
/// to keep the wearer off the furniture.
struct VRPlaySpace {
    /// Pose of the scene origin in the ARKit world.
    private(set) var worldFromScene: VRPose = .identity
    /// World height of the floor, once ARKit has found it.
    private(set) var floorHeight: Float?
    /// Eye height assumed until a floor is found.
    var fallbackEyeHeight: Float = 1.6
    /// Centre of the circular play area on the floor, world x and z.
    private(set) var boundaryCenter: SIMD2<Float> = .zero
    var boundaryRadius: Float = 1.5

    var sceneFromWorld: VRPose { worldFromScene.inverse }

    /// Points the scene's -Z where the head faces and puts the scene origin
    /// under the head. Keeps gravity: only yaw changes.
    mutating func recenter(head worldFromScreen: VRPose) {
        let heading = VRMath.heading(of: worldFromScreen.rotation)
        let p = worldFromScreen.position
        let floor = floorHeight ?? (p.y - fallbackEyeHeight)
        worldFromScene = VRPose(rotation: VRMath.rotationY(heading), position: SIMD3(p.x, floor, p.z))
        boundaryCenter = SIMD2(p.x, p.z)
    }

    mutating func setFloorHeight(_ height: Float) {
        floorHeight = height
        worldFromScene.position.y = height
    }

    /// Turns the wearer by `angle` radians (positive turns right) about the
    /// vertical line through the head.
    mutating func snapTurn(by angle: Float, head worldFromScreen: VRPose) {
        let pivot = SIMD3(worldFromScreen.position.x, 0, worldFromScreen.position.z)
        let turn = VRMath.rotationY(angle)
        let rotated = turn.act(worldFromScene.position - pivot) + pivot
        worldFromScene = VRPose(rotation: (turn * worldFromScene.rotation).normalized, position: rotated)
    }

    /// Moves the wearer through the scene. `stick.y` walks along the head's
    /// heading and `stick.x` strafes right, at `speed` meters per second.
    mutating func move(stick: SIMD2<Float>, speed: Float, dt: Float, head worldFromScreen: VRPose) {
        guard simd_length(stick) > 0, dt > 0 else { return }
        let heading = VRMath.heading(of: worldFromScreen.rotation)
        let forward = SIMD3(-sin(heading), 0, -cos(heading))
        let right = SIMD3(cos(heading), 0, -sin(heading))
        let step = (forward * stick.y + right * stick.x) * speed * dt
        worldFromScene.position -= step
    }

    /// Signed distance from the head to the play-area edge: positive inside.
    func boundaryDistance(head position: SIMD3<Float>) -> Float {
        boundaryRadius - simd_length(SIMD2(position.x, position.z) - boundaryCenter)
    }

    /// The play-area centre on the floor, in scene coordinates.
    var boundaryCenterInScene: SIMD3<Float> {
        sceneFromWorld.transformPoint(SIMD3(boundaryCenter.x, floorHeight ?? worldFromScene.position.y, boundaryCenter.y))
    }
}
