import SwiftUI

/// Registration entry for the App Attest experiment.
enum AppAttestExperiment {
    static let experiment = Experiment(
        id: "app-attest",
        title: "App Attest",
        summary: "Sign in with Apple. Each whoami is a fresh App Attest assertion.",
        icon: "checkmark.shield"
    ) {
        AppAttestView()
    }
}
