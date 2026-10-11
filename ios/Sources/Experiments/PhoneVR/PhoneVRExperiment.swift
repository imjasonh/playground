import SwiftUI

/// Registration entry for the Phone VR experiment.
enum PhoneVRExperiment {
    static let experiment = Experiment(
        id: "phone-vr",
        title: "Phone VR",
        summary: "6DoF VR in a lens viewer: ARKit and gyro tracking, Metal stereo, lens correction, and timewarp.",
        icon: "binoculars"
    ) {
        PhoneVRView()
    }
}
