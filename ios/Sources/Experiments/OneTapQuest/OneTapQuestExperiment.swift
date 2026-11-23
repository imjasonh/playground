import SwiftUI

/// Registration entry for the One Tap Quest Godot experiment.
enum OneTapQuestExperiment {
    static let experiment = Experiment(
        id: "one-tap-quest",
        title: "One Tap Quest",
        summary: "Godot one-tap RPG: drag to aim, release to march north, and topple the boss.",
        icon: "figure.walk"
    ) {
        OneTapQuestView()
    }
}
