import Foundation
import simd

/// CPU-side triangle mesh for one chunk of voxels, ready to be wrapped in
/// SceneKit geometry sources on the rendering side.
struct VoxelMeshData {
    var positions: [SIMD3<Float>] = []
    var normals: [SIMD3<Float>] = []
    /// Per-vertex RGBA with face shading baked in (rendered unlit).
    var colors: [SIMD4<Float>] = []
    var indices: [UInt32] = []

    var isEmpty: Bool { indices.isEmpty }
    /// Number of emitted quads (each quad is two triangles).
    var faceCount: Int { indices.count / 6 }
}

/// Turns voxels into cube faces, culling any face that touches an occupied
/// neighbor (those faces are interior and would only z-fight).
enum VoxelMesher {
    struct Face {
        let offset: (x: Int32, y: Int32, z: Int32)
        let normal: SIMD3<Float>
        /// Brightness multiplier baked into vertex colors. The mesh renders
        /// with a constant (unlit) lighting model, so shading each face
        /// direction differently is what makes individual cubes readable.
        let shade: Float
        /// Corner offsets within the unit cube, quad order.
        let corners: [SIMD3<Float>]
    }

    static let faces: [Face] = [
        Face(
            offset: (0, 1, 0),
            normal: SIMD3(0, 1, 0),
            shade: 1.0,
            corners: [SIMD3(0, 1, 0), SIMD3(0, 1, 1), SIMD3(1, 1, 1), SIMD3(1, 1, 0)]
        ),
        Face(
            offset: (0, -1, 0),
            normal: SIMD3(0, -1, 0),
            shade: 0.45,
            corners: [SIMD3(0, 0, 0), SIMD3(1, 0, 0), SIMD3(1, 0, 1), SIMD3(0, 0, 1)]
        ),
        Face(
            offset: (1, 0, 0),
            normal: SIMD3(1, 0, 0),
            shade: 0.8,
            corners: [SIMD3(1, 0, 0), SIMD3(1, 1, 0), SIMD3(1, 1, 1), SIMD3(1, 0, 1)]
        ),
        Face(
            offset: (-1, 0, 0),
            normal: SIMD3(-1, 0, 0),
            shade: 0.65,
            corners: [SIMD3(0, 0, 0), SIMD3(0, 0, 1), SIMD3(0, 1, 1), SIMD3(0, 1, 0)]
        ),
        Face(
            offset: (0, 0, 1),
            normal: SIMD3(0, 0, 1),
            shade: 0.9,
            corners: [SIMD3(0, 0, 1), SIMD3(1, 0, 1), SIMD3(1, 1, 1), SIMD3(0, 1, 1)]
        ),
        Face(
            offset: (0, 0, -1),
            normal: SIMD3(0, 0, -1),
            shade: 0.55,
            corners: [SIMD3(0, 0, 0), SIMD3(0, 1, 0), SIMD3(1, 1, 0), SIMD3(1, 0, 0)]
        ),
    ]

    /// Meshes `voxels` (one chunk's worth) in world coordinates.
    /// `isOccupied` answers for the *whole* grid so faces against voxels in
    /// neighboring chunks are culled too. Output order is deterministic.
    static func mesh(
        voxels: [VoxelKey: VoxelData],
        voxelSize: Float,
        isOccupied: (VoxelKey) -> Bool
    ) -> VoxelMeshData {
        var mesh = VoxelMeshData()
        let sortedKeys = voxels.keys.sorted { lhs, rhs in
            (lhs.x, lhs.y, lhs.z) < (rhs.x, rhs.y, rhs.z)
        }

        for key in sortedKeys {
            guard let data = voxels[key] else { continue }
            let origin = SIMD3<Float>(Float(key.x), Float(key.y), Float(key.z)) * voxelSize

            for face in faces {
                let neighbor = VoxelKey(
                    x: key.x + face.offset.x,
                    y: key.y + face.offset.y,
                    z: key.z + face.offset.z
                )
                if isOccupied(neighbor) { continue }

                let base = UInt32(mesh.positions.count)
                let color = SIMD4<Float>(data.color * face.shade, 1)
                for corner in face.corners {
                    mesh.positions.append(origin + corner * voxelSize)
                    mesh.normals.append(face.normal)
                    mesh.colors.append(color)
                }
                mesh.indices.append(contentsOf: [base, base + 1, base + 2, base, base + 2, base + 3])
            }
        }
        return mesh
    }
}
