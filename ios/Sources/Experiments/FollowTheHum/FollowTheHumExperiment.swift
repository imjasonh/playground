import SwiftUI

/// Registration entry for the Follow the Hum experiment.
enum FollowTheHumExperiment {
    static let experiment = Experiment(
        id: "follow-the-hum",
        title: "Follow the Hum",
        summary: "Hide a nearby spot and find it with a head-tracked AirPods hum.",
        icon: "waveform.circle"
    ) {
        FollowTheHumView()
    }
}
