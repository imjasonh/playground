import SwiftUI

/// Registration entry for the Blather experiment.
enum BlatherExperiment {
    static let experiment = Experiment(
        id: "blather",
        title: "Blather",
        summary: "Spoken episodes on a topic, with cover art and audio saved on this device.",
        icon: "mic"
    ) {
        BlatherView()
    }
}
