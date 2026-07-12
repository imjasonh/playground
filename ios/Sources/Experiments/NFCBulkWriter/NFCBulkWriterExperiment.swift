import SwiftUI

/// Registration entry for the NFC Bulk Writer experiment.
enum NFCBulkWriterExperiment {
    static let experiment = Experiment(
        id: "nfc-bulk-writer",
        title: "NFC Bulk Writer",
        summary: "Set one NDEF payload, then tap tags to write it until you stop.",
        icon: "wave.3.right"
    ) {
        NFCBulkWriterView()
    }
}
