import SwiftUI

/// Registration entry for the NFC Tags experiment.
enum NFCTagsExperiment {
    static let experiment = Experiment(
        id: "nfc-tags",
        title: "NFC Tags",
        summary: "Read and write NFC tags (NDEF text/URL), including blank NTAGs.",
        icon: "wave.3.right"
    ) {
        NFCTagsView()
    }
}
