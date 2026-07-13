import SwiftUI

/// Registration entry for the Voxel World experiment.
enum VoxelWorldExperiment {
    static let experiment = Experiment(
        id: "voxel-world",
        title: "Voxel World",
        summary: "ARKit rebuilds the room as Minecraft-style palette blocks — dial the block size up and down.",
        icon: "cube.transparent"
    ) {
        VoxelWorldView()
    }
}
