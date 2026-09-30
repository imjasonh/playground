import SwiftUI

/// Registration entry for the Hair Color experiment.
enum HairColorExperiment {
    static let experiment = Experiment(
        id: "hair-color",
        title: "Hair Color",
        summary: "Live camera hair tint. Vision isolates hair on device and Core Image dyes those pixels.",
        icon: "paintpalette.fill"
    ) {
        HairColorView()
    }
}
