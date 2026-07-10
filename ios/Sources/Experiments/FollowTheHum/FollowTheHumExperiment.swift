import SwiftUI

/// Registration entry for the Follow the Hum experiment.
enum FollowTheHumExperiment {
    static let experiment = Experiment(
        id: "follow-the-hum",
        title: "Follow the Hum",
        summary: "A nearby spot is hidden — follow a spatial hum in your AirPods to find it.",
        icon: "waveform.circle"
    ) {
        FollowTheHumView()
    }
}
