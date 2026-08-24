import SwiftUI

enum DoomFaceExperiment {
    static let experiment = Experiment(
        id: "doom-face",
        title: "Doom Face",
        summary: "Stamp your face onto doomguy's status-bar sheet, then export a GIF.",
        icon: "face.smiling.inverse"
    ) {
        DoomFaceView()
    }
}
