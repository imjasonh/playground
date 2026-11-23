import SwiftUI

/// Registration entry for the One Tap Quest Godot experiment.
enum OneTapQuestExperiment {
    static let experiment = Experiment(
        id: "one-tap-quest",
        title: "One Tap Quest",
        summary: "Unofficial AI-built Godot recreation of One Tap Quest by shimage.net.",
        icon: "figure.walk"
    ) {
        OneTapQuestView()
    }
}
