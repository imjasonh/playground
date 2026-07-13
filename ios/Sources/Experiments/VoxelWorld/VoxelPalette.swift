import simd

/// Fixed Minecraft-style block palette. Sampled camera colors are snapped to
/// the nearest entry at mesh time, so the world reads as stylized blocks
/// instead of muddy real-world color — fidelity is explicitly not the goal.
/// (The raw running average is still stored per voxel, so a color can settle
/// across a palette boundary as a voxel is re-observed.)
enum VoxelPalette {
    /// Linear-ish RGB in `0...1`, loosely after Minecraft block/wool colors:
    /// grasses, dirts, woods, stones, sand, brick, wools, water blues.
    static let colors: [SIMD3<Float>] = [
        SIMD3(0.42, 0.66, 0.31), // grass green
        SIMD3(0.50, 0.72, 0.16), // lime
        SIMD3(0.23, 0.37, 0.15), // dark foliage
        SIMD3(0.52, 0.38, 0.26), // dirt
        SIMD3(0.44, 0.28, 0.17), // brown wool
        SIMD3(0.36, 0.25, 0.16), // dark oak
        SIMD3(0.45, 0.33, 0.20), // spruce
        SIMD3(0.72, 0.58, 0.36), // oak plank
        SIMD3(0.77, 0.71, 0.48), // birch
        SIMD3(0.86, 0.82, 0.63), // sand
        SIMD3(0.97, 0.99, 0.99), // snow
        SIMD3(0.93, 0.93, 0.91), // white wool
        SIMD3(0.78, 0.78, 0.76), // light gray
        SIMD3(0.65, 0.65, 0.65), // cobblestone
        SIMD3(0.50, 0.50, 0.50), // stone
        SIMD3(0.39, 0.43, 0.44), // gray wool
        SIMD3(0.31, 0.31, 0.33), // deepslate
        SIMD3(0.11, 0.11, 0.13), // black
        SIMD3(0.65, 0.28, 0.23), // brick
        SIMD3(0.63, 0.15, 0.13), // red wool
        SIMD3(0.38, 0.19, 0.19), // netherrack
        SIMD3(0.82, 0.47, 0.20), // terracotta orange
        SIMD3(0.91, 0.75, 0.21), // yellow
        SIMD3(0.84, 0.54, 0.62), // pink
        SIMD3(0.48, 0.25, 0.65), // purple
        SIMD3(0.24, 0.35, 0.68), // water blue
        SIMD3(0.36, 0.62, 0.83), // light blue
        SIMD3(0.08, 0.53, 0.53), // cyan
    ]

    /// Nearest palette entry by perceptually-weighted RGB distance
    /// (green differences matter most to the eye, blue least).
    static func quantize(_ color: SIMD3<Float>) -> SIMD3<Float> {
        var best = colors[0]
        var bestDistance = Float.greatestFiniteMagnitude
        for candidate in colors {
            let d = distanceSquared(candidate, color)
            if d < bestDistance {
                bestDistance = d
                best = candidate
            }
        }
        return best
    }

    static func distanceSquared(_ a: SIMD3<Float>, _ b: SIMD3<Float>) -> Float {
        let diff = a - b
        let weighted = diff * diff * SIMD3<Float>(2, 4, 3)
        return weighted.x + weighted.y + weighted.z
    }
}
