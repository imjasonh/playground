import SwiftUI

/// Registration entry for the Local Lens experiment.
enum LocalLensExperiment {
    static let experiment = Experiment(
        id: "local-lens",
        title: "Local Lens",
        summary: "Live on-device Vision — classify, OCR, face/eye landmarks, body & hand pose, codes. No network.",
        icon: "camera.viewfinder"
    ) {
        LocalLensView()
    }
}
