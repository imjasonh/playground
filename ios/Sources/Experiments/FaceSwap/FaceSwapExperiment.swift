import SwiftUI

/// Registration entry for the Face Swap experiment.
enum FaceSwapExperiment {
    static let experiment = Experiment(
        id: "face-swap",
        title: "Face Swap",
        summary: "On-device model chooses targeted edits, then changes only the regions those tools name.",
        icon: "person.crop.rectangle"
    ) {
        FaceSwapView()
    }
}
