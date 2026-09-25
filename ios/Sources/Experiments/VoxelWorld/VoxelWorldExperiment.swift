import SwiftUI

/// Registration entry for the Voxel World experiment.
enum VoxelWorldExperiment {
    static let experiment = Experiment(
        id: "voxel-world",
        title: "Voxel World",
        summary: "ARKit rebuilds the room as Minecraft-style palette blocks.",
        icon: "cube.transparent"
    ) {
        VoxelWorldView()
    }
}
