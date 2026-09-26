import SwiftUI

/// Registration entry for the Voxel Eyes experiment.
enum VoxelWorldExperiment {
    static let experiment = Experiment(
        id: "voxel-world",
        title: "Voxel Eyes",
        summary: "ARKit rebuilds the room as Minecraft-style palette blocks.",
        icon: "cube.transparent"
    ) {
        VoxelWorldView()
    }
}
