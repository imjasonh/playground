import SwiftUI

/// Registration entry for the Doom Face experiment.
enum DoomFaceExperiment {
    static let experiment = Experiment(
        id: "doom-face",
        title: "Doom Face",
        summary: "Match your mug to doomguy’s status-bar faces, stamp the sheet, export a GIF.",
        icon: "face.smiling.inverse"
    ) {
        DoomFaceView()
    }
}
