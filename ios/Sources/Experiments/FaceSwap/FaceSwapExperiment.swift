import SwiftUI

/// Registration entry for the Face Swap experiment.
enum FaceSwapExperiment {
    static let experiment = Experiment(
        id: "face-swap",
        title: "Face Swap",
        summary: "On-device model traces face outlines, then reconstructs only inside those outlines.",
        icon: "person.crop.rectangle"
    ) {
        FaceSwapView()
    }
}
