import SwiftUI

/// Registration entry for the App Attest experiment.
enum AppAttestExperiment {
    static let experiment = Experiment(
        id: "app-attest",
        title: "App Attest",
        summary: "Attest this device once, then call a Worker that only returns the bound user and device ids.",
        icon: "checkmark.shield"
    ) {
        AppAttestView()
    }
}
