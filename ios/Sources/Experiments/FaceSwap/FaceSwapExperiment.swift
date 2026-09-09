import SwiftUI

/// Registration entry for the Face Swap experiment.
enum FaceSwapExperiment {
    static let experiment = Experiment(
        id: "face-swap",
        title: "Face Swap",
        summary: "On-device model chooses face contours, then reconstructs only inside them.",
        icon: "person.crop.rectangle"
    ) {
        FaceSwapView()
    }
}
