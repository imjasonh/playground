import Foundation
import simd

/// Integer coordinate of one voxel in the world-aligned grid.
/// A world point `p` maps to `floor(p / voxelSize)` on each axis.
struct VoxelKey: Hashable {
    var x: Int32
    var y: Int32
    var z: Int32
}

/// Integer coordinate of a chunk — a cube of `chunkSize³` voxels that is
/// meshed and rendered as one unit, so a new voxel only rebuilds its chunk.
struct VoxelChunkKey: Hashable {
    var x: Int32
    var y: Int32
    var z: Int32
}

/// Per-voxel color, refined as more camera samples land in the same cell.
/// A capped running average keeps early noisy samples from dominating while
/// still letting the color settle as the phone re-observes the voxel.
///
/// Also tracks free-space evidence: when the camera repeatedly sees *through*
/// the cell (the observed surface is well behind it), the voxel is carved
/// away, so moved objects and depth-noise floaters clean themselves up.
struct VoxelData: Equatable {
    /// Average linear RGB in `0...1`.
    private(set) var color: SIMD3<Float>
    private(set) var sampleWeight: Float
    /// Consecutive integrations that observed free space through this voxel.
    private(set) var missCount = 0

    static let maxSampleWeight: Float = 64
    /// Free-space observations required before a voxel is carved away.
    /// (>1 so one noisy depth frame can't delete real geometry.)
    static let removalMissThreshold = 3

    init(color: SIMD3<Float>) {
        self.color = color
        self.sampleWeight = 1
    }

    mutating func addSample(_ sample: SIMD3<Float>) {
        let newWeight = min(sampleWeight + 1, Self.maxSampleWeight)
        color += (sample - color) / newWeight
        sampleWeight = newWeight
        missCount = 0
    }

    /// The camera saw a surface at this voxel's depth again.
    mutating func registerConfirmation() {
        missCount = 0
    }

    /// The camera saw free space through this voxel. Returns `true` when the
    /// miss threshold is reached and the voxel should be removed.
    mutating func registerMiss() -> Bool {
        missCount += 1
        return missCount >= Self.removalMissThreshold
    }
}

/// Sparse world-aligned voxel volume, stored per chunk.
///
/// Not thread-safe: the AR session confines all mutation to one queue.
struct VoxelGrid {
    enum AddResult: Equatable {
        /// A new voxel appeared at this key.
        case added(VoxelKey)
        /// An existing voxel's color was refined.
        case updated(VoxelKey)
        /// The voxel budget is full and this sample would create a new voxel.
        case rejectedBudget
        /// Non-finite or absurdly distant world point.
        case rejectedInvalid
    }

    let voxelSize: Float
    let chunkSize: Int32

    private(set) var chunks: [VoxelChunkKey: [VoxelKey: VoxelData]] = [:]
    private(set) var voxelCount = 0

    init(voxelSize: Float, chunkSize: Int32 = 8) {
        self.voxelSize = max(voxelSize, 0.001)
        self.chunkSize = max(chunkSize, 1)
    }

    func key(for point: SIMD3<Float>) -> VoxelKey {
        VoxelKey(
            x: Int32((point.x / voxelSize).rounded(.down)),
            y: Int32((point.y / voxelSize).rounded(.down)),
            z: Int32((point.z / voxelSize).rounded(.down))
        )
    }

    func chunkKey(for key: VoxelKey) -> VoxelChunkKey {
        VoxelChunkKey(
            x: Self.floorDiv(key.x, chunkSize),
            y: Self.floorDiv(key.y, chunkSize),
            z: Self.floorDiv(key.z, chunkSize)
        )
    }

    /// World-space center of a voxel cell.
    func center(of key: VoxelKey) -> SIMD3<Float> {
        (SIMD3<Float>(Float(key.x), Float(key.y), Float(key.z)) + SIMD3<Float>(repeating: 0.5)) * voxelSize
    }

    func data(for key: VoxelKey) -> VoxelData? {
        chunks[chunkKey(for: key)]?[key]
    }

    func isOccupied(_ key: VoxelKey) -> Bool {
        data(for: key) != nil
    }

    func voxels(in chunk: VoxelChunkKey) -> [VoxelKey: VoxelData] {
        chunks[chunk] ?? [:]
    }

    mutating func addSample(worldPoint: SIMD3<Float>, color: SIMD3<Float>, maxVoxels: Int) -> AddResult {
        guard
            worldPoint.x.isFinite, worldPoint.y.isFinite, worldPoint.z.isFinite,
            abs(worldPoint.x) < 1_000, abs(worldPoint.y) < 1_000, abs(worldPoint.z) < 1_000
        else {
            return .rejectedInvalid
        }

        let key = self.key(for: worldPoint)
        let chunk = chunkKey(for: key)
        if var existing = chunks[chunk]?[key] {
            existing.addSample(color)
            chunks[chunk]?[key] = existing
            return .updated(key)
        }
        guard voxelCount < maxVoxels else { return .rejectedBudget }
        chunks[chunk, default: [:]][key] = VoxelData(color: color)
        voxelCount += 1
        return .added(key)
    }

    /// Registers a free-space observation for an existing voxel. Returns
    /// `true` when the miss threshold was reached and the voxel was removed
    /// (freeing budget for new voxels).
    mutating func registerMiss(at key: VoxelKey) -> Bool {
        let chunk = chunkKey(for: key)
        guard var data = chunks[chunk]?[key] else { return false }
        if data.registerMiss() {
            chunks[chunk]?.removeValue(forKey: key)
            if chunks[chunk]?.isEmpty == true {
                chunks.removeValue(forKey: chunk)
            }
            voxelCount -= 1
            return true
        }
        chunks[chunk]?[key] = data
        return false
    }

    /// Resets free-space evidence after the voxel was re-observed as surface.
    mutating func registerConfirmation(at key: VoxelKey) {
        let chunk = chunkKey(for: key)
        guard var data = chunks[chunk]?[key] else { return }
        data.registerConfirmation()
        chunks[chunk]?[key] = data
    }

    /// Chunks whose cached mesh is stale after the voxel at `key` changed:
    /// its own chunk, plus any face-adjacent chunk holding an occupied
    /// neighbor (that neighbor's face toward `key` may now be hidden).
    func affectedChunks(around key: VoxelKey) -> Set<VoxelChunkKey> {
        let home = chunkKey(for: key)
        var result: Set<VoxelChunkKey> = [home]
        for offset in Self.faceNeighborOffsets {
            let neighbor = VoxelKey(x: key.x + offset.x, y: key.y + offset.y, z: key.z + offset.z)
            let neighborChunk = chunkKey(for: neighbor)
            if neighborChunk != home, isOccupied(neighbor) {
                result.insert(neighborChunk)
            }
        }
        return result
    }

    mutating func removeAll() {
        chunks.removeAll()
        voxelCount = 0
    }

    static let faceNeighborOffsets: [(x: Int32, y: Int32, z: Int32)] = [
        (1, 0, 0), (-1, 0, 0),
        (0, 1, 0), (0, -1, 0),
        (0, 0, 1), (0, 0, -1),
    ]

    /// Integer division that rounds toward negative infinity (so voxel −1
    /// lands in chunk −1, not chunk 0).
    static func floorDiv(_ a: Int32, _ b: Int32) -> Int32 {
        let quotient = a / b
        let remainder = a % b
        if remainder != 0 && ((remainder < 0) != (b < 0)) {
            return quotient - 1
        }
        return quotient
    }
}

/// Maps a unit slider `0...1` onto a voxel edge length, log-scaled.
///
/// The floor is deliberately chunky (10 cm): the LiDAR depth map is only
/// 256×192 with centimeter-level noise, so small voxels expose the sensor
/// (fuzzy multi-voxel-thick walls) instead of looking Minecraft-crisp.
enum VoxelSizeMapping {
    static let minimumSize: Float = 0.10
    static let maximumSize: Float = 0.50
    static let defaultSize: Float = 0.25

    static func size(sliderValue: Double) -> Float {
        let t = Float(min(max(sliderValue, 0), 1))
        return minimumSize * powf(maximumSize / minimumSize, t)
    }

    static func sliderValue(for size: Float) -> Double {
        let clamped = min(max(size, minimumSize), maximumSize)
        return Double(logf(clamped / minimumSize) / logf(maximumSize / minimumSize))
    }

    static func label(for size: Float) -> String {
        let centimeters = size * 100
        let rounded = centimeters.rounded()
        if abs(centimeters - rounded) < 0.05 {
            return String(format: "%.0f cm", rounded)
        }
        return String(format: "%.1f cm", centimeters)
    }
}
