import SwiftUI

/// Registration entry for the Blather experiment.
enum BlatherExperiment {
    static let experiment = Experiment(
        id: "blather",
        title: "Blather",
        summary: "On-device speech that keeps talking about your topic and saves the audio on this device.",
        icon: "waveform"
    ) {
        BlatherView()
    }
}
