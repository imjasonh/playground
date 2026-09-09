import SwiftUI

/// Registration entry for the Face Swap experiment.
enum FaceSwapExperiment {
    static let experiment = Experiment(
        id: "face-swap",
        title: "Face Swap",
        summary: "On-device model chooses a targeted edit. The rest of the photo stays as it was.",
        icon: "person.crop.rectangle"
    ) {
        FaceSwapView()
    }
}
