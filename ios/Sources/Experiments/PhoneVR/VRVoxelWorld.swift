import CoreVideo
import Foundation
import Metal
import simd

/// Head-lamp falloff for Minecraft: full brightness nearby, black past the
/// LiDAR range, so unsampled space reads as a dark mine instead of a
/// pixelized camera shell.
enum VRTorchLight {
    /// Distance that stays at full brightness, meters.
    static let innerMeters: Float = 1.2
    /// Distance that reaches black, meters. Matches Apple's LiDAR maximum
    /// closely enough that beyond-range samples never show.
    static let outerMeters: Float = 4.5

    /// Quadratic falloff: 1 inside `inner`, 0 at `outer` and beyond.
    static func attenuation(distance: Float, inner: Float = innerMeters, outer: Float = outerMeters) -> Float {
        guard distance.isFinite, outer > inner else { return 0 }
        if distance <= inner { return 1 }
        if distance >= outer { return 0 }
        let t = (outer - distance) / (outer - inner)
        return t * t
    }
}

/// GPU mesh for one voxel chunk, positions in ARKit world coordinates.
struct VRVoxelMeshChunk {
    var vertices: MTLBuffer
    var indices: MTLBuffer
    var indexCount: Int
}

struct VRVoxelSnapshot {
    var chunks: [VRVoxelMeshChunk]
    var voxelCount: Int
}

/// One camera frame to fold into the Minecraft voxel grid.
struct VRVoxelCaptureFrame {
    var capturedImage: CVPixelBuffer
    var depthMap: CVPixelBuffer?
    var confidenceMap: CVPixelBuffer?
    var featurePoints: [SIMD3<Float>]?
    var intrinsics: simd_float3x3
    var cameraTransform: simd_float4x4
    var timestamp: TimeInterval
}

/// Converts a Voxel Eyes CPU mesh into the VR scene vertex layout.
enum VRVoxelGeometry {
    static func sceneVertices(from mesh: VoxelMeshData) -> [VRSceneVertex] {
        var vertices: [VRSceneVertex] = []
        vertices.reserveCapacity(mesh.positions.count)
        for i in mesh.positions.indices {
            let rgb = SIMD3(mesh.colors[i].x, mesh.colors[i].y, mesh.colors[i].z)
            vertices.append(
                VRSceneVertex(position: mesh.positions[i], normal: mesh.normals[i], color: VRPalette.packLinear(rgb))
            )
        }
        return vertices
    }
}

/// World-aligned voxel volume for Phone VR Minecraft, built with the same
/// scanner as Voxel Eyes. Chunks are meshed on a background queue and the
/// render thread reads a snapshot of Metal buffers. The grid stays in ARKit
/// world space so looking around does not swim the blocks; the eye pass
/// applies `sceneFromWorld` as the model matrix.
final class VRVoxelWorld: @unchecked Sendable {
    static let maxVoxels = VoxelWorldSession.maxVoxels
    static let maxDepthMeters = VoxelWorldSession.maxDepthMeters
    static let voxelEdgeMeters = VoxelWorldSession.voxelEdgeMeters
    static let integrationInterval = VoxelWorldSession.integrationInterval
    static let rebuildBudgetPerTick = VoxelWorldSession.rebuildBudgetPerTick

    private let device: MTLDevice
    private let processingQueue = DispatchQueue(label: "PhoneVR.voxels", qos: .userInitiated)
    private let published = VRLocked(VRVoxelSnapshot(chunks: [], voxelCount: 0))

    /// Confined to `processingQueue` after init.
    private var grid = VoxelGrid(voxelSize: VRVoxelWorld.voxelEdgeMeters)
    private var structuralDirty: Set<VoxelChunkKey> = []
    private var colorDirty: Set<VoxelChunkKey> = []
    private var gpuChunks: [VoxelChunkKey: VRVoxelMeshChunk] = [:]
    private var paletteSignature: [VoxelChunkKey: Int] = [:]
    private var lastTimestamp: TimeInterval = -1
    private var integrating = false
    private var active = false

    init(device: MTLDevice) {
        self.device = device
    }

    var snapshot: VRVoxelSnapshot { published.get() }

    /// Starts or stops consuming camera frames. Voxels already captured stay
    /// so switching scenes and back does not empty the room.
    func setActive(_ active: Bool) {
        processingQueue.async { self.active = active }
    }

    /// Queues one frame for integration. Drops the frame when a previous
    /// tick is still running or the timestamp is not newer.
    func ingest(_ frame: VRVoxelCaptureFrame) {
        processingQueue.async { [weak self] in
            self?.integrate(frame)
        }
    }

    private func integrate(_ frame: VRVoxelCaptureFrame) {
        guard active else { return }
        guard !integrating else { return }
        guard frame.timestamp - lastTimestamp >= Self.integrationInterval else { return }
        integrating = true
        lastTimestamp = frame.timestamp
        defer { integrating = false }

        let result = VoxelScanner.integrate(
            grid: &grid,
            intrinsics: frame.intrinsics,
            cameraTransform: frame.cameraTransform,
            capturedImage: frame.capturedImage,
            depthMap: frame.depthMap,
            confidenceMap: frame.confidenceMap,
            featurePoints: frame.featurePoints,
            maxVoxels: Self.maxVoxels,
            maxDepth: Self.maxDepthMeters
        )
        structuralDirty.formUnion(result.structural)
        colorDirty.formUnion(result.color)
        rebuildDirtyChunks()
    }

    private func rebuildDirtyChunks() {
        var toRebuild: [VoxelChunkKey] = []
        while toRebuild.count < Self.rebuildBudgetPerTick, let chunk = structuralDirty.popFirst() {
            toRebuild.append(chunk)
            colorDirty.remove(chunk)
        }
        while toRebuild.count < Self.rebuildBudgetPerTick, let chunk = colorDirty.popFirst() {
            let signature = Self.signature(of: grid.voxels(in: chunk))
            if paletteSignature[chunk] == signature {
                continue
            }
            toRebuild.append(chunk)
        }
        guard !toRebuild.isEmpty else { return }

        var changed = false
        for chunk in toRebuild {
            let voxels = grid.voxels(in: chunk)
            let signature = Self.signature(of: voxels)
            if voxels.isEmpty {
                if gpuChunks.removeValue(forKey: chunk) != nil { changed = true }
                paletteSignature.removeValue(forKey: chunk)
                continue
            }
            let mesh = VoxelMesher.mesh(
                voxels: voxels,
                voxelSize: grid.voxelSize,
                isOccupied: { self.grid.isOccupied($0) }
            )
            guard let gpu = makeGPUChunk(from: mesh) else {
                if gpuChunks.removeValue(forKey: chunk) != nil { changed = true }
                paletteSignature.removeValue(forKey: chunk)
                continue
            }
            gpuChunks[chunk] = gpu
            paletteSignature[chunk] = signature
            changed = true
        }
        if changed {
            publish()
        }
    }

    private func publish() {
        let snapshot = VRVoxelSnapshot(
            chunks: Array(gpuChunks.values),
            voxelCount: grid.voxelCount
        )
        published.set(snapshot)
    }

    private func makeGPUChunk(from mesh: VoxelMeshData) -> VRVoxelMeshChunk? {
        guard !mesh.isEmpty else { return nil }
        let vertices = VRVoxelGeometry.sceneVertices(from: mesh)
        guard
            let vertexBuffer = device.makeBuffer(
                bytes: vertices,
                length: vertices.count * MemoryLayout<VRSceneVertex>.stride,
                options: .storageModeShared
            ),
            let indexBuffer = device.makeBuffer(
                bytes: mesh.indices,
                length: mesh.indices.count * MemoryLayout<UInt32>.stride,
                options: .storageModeShared
            )
        else {
            return nil
        }
        vertexBuffer.label = "minecraft voxels"
        indexBuffer.label = "minecraft voxel indices"
        return VRVoxelMeshChunk(vertices: vertexBuffer, indices: indexBuffer, indexCount: mesh.indices.count)
    }

    /// Hash of each occupied cell's palette color, so a color-only tick that
    /// has not crossed a palette boundary can skip a remesh. That is what
    /// keeps faces from shimmering while the running average settles.
    static func signature(of voxels: [VoxelKey: VoxelData]) -> Int {
        var hasher = Hasher()
        let keys = voxels.keys.sorted { lhs, rhs in
            (lhs.x, lhs.y, lhs.z) < (rhs.x, rhs.y, rhs.z)
        }
        for key in keys {
            guard let data = voxels[key] else { continue }
            let q = VoxelPalette.quantize(data.color)
            hasher.combine(key.x)
            hasher.combine(key.y)
            hasher.combine(key.z)
            hasher.combine(Int((q.x * 255).rounded()))
            hasher.combine(Int((q.y * 255).rounded()))
            hasher.combine(Int((q.z * 255).rounded()))
        }
        return hasher.finalize()
    }
}
