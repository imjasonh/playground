import SwiftUI

/// Registration entry for the Snore Log experiment.
enum SnoreLogExperiment {
    static let experiment = Experiment(
        id: "snore-log",
        title: "Snore Log",
        summary: "Listen while you sleep; save short clips when snoring is detected.",
        icon: "moon.zzz"
    ) {
        SnoreLogView()
    }
}
