import SwiftUI

/// Registration entry for the NFC Tags experiment.
enum NFCTagsExperiment {
    static let experiment = Experiment(
        id: "nfc-tags",
        title: "NFC Tags",
        summary: "Read and write NDEF text or URL tags with Core NFC.",
        icon: "wave.3.right.circle"
    ) {
        NFCTagsView()
    }
}
