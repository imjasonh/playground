import SwiftUI

/// Registration entry for the Hair Color experiment.
enum HairColorExperiment {
    static let experiment = Experiment(
        id: "hair-color",
        title: "Hair Color",
        summary: "Live camera hair tint. Dyes pixels that match the hair above your face, including bangs and long hair.",
        icon: "paintpalette.fill"
    ) {
        HairColorView()
    }
}
