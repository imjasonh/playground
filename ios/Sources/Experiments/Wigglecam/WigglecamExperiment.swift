import SwiftUI

/// Registration entry for the Wigglecam experiment.
enum WigglecamExperiment {
    static let experiment = Experiment(
        id: "wigglecam",
        title: "Wigglecam",
        summary: "Dual-wide wigglegrams — AE-locked capture, tone-matched GIF/JPEGs to Photos.",
        icon: "rectangle.on.rectangle.angled"
    ) {
        WigglecamView()
    }
}
