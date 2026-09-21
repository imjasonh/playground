import SwiftUI

/// Registration entry for the Laya typed-decision experiment.
///
/// The download, tokenizer, and Core ML runtime live in `Shared/Laya` so
/// Army List can load the same bundle.
enum LayaExperiment {
    static let experiment = Experiment(
        id: "laya",
        title: "Laya",
        summary: "Download the laya-coreml ANE bundle and ask it choice, score, or yes/no questions about a text; probabilities come back in one Core ML pass.",
        icon: "brain"
    ) {
        LayaView()
    }
}
