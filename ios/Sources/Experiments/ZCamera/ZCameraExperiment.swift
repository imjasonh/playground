import SwiftUI

/// Registration entry for the Z-Camera experiment.
enum ZCameraExperiment {
    static let experiment = Experiment(
        id: "z-camera",
        title: "Z-Camera",
        summary: "Only show what’s inside a depth band — smooth depth overlay, higher-res capture.",
        icon: "square.3.layers.3d.down.right"
    ) {
        ZCameraView()
    }
}
