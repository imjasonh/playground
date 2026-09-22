import SwiftUI

/// Registration entry for the Live Translate experiment.
enum LiveTranslateExperiment {
    static let experiment = Experiment(
        id: "live-translate",
        title: "Live Translate",
        summary: "Point the camera at text. The on-device model covers it with a translation and copies that text.",
        icon: "translate"
    ) {
        LiveTranslateView()
    }
}
