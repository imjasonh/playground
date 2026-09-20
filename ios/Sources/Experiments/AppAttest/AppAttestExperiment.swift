import SwiftUI

/// Registration entry for the App Attest experiment.
enum AppAttestExperiment {
    static let experiment = Experiment(
        id: "app-attest",
        title: "App Attest",
        summary: "Sign in with Apple. The Worker returns the attested Apple user id and device id.",
        icon: "checkmark.shield"
    ) {
        AppAttestView()
    }
}
