import SwiftUI

/// Registration entry for the GCP Auth experiment.
enum GCPAuthExperiment {
    static let experiment = Experiment(
        id: "gcp-auth",
        title: "GCP Auth",
        summary: "App Attest → Firebase App Check → Firebase Auth → Workload Identity Federation, with no key shipped in the app.",
        icon: "lock.shield"
    ) {
        GCPAuthView()
    }
}
