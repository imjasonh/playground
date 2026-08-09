import SwiftUI

/// Registration entry for the Container Lab experiment.
enum ContainerLabExperiment {
    static let experiment = Experiment(
        id: "container-lab",
        title: "Container Lab",
        summary: "Pull a container image to an on-device OCI layout, and test whether WebKit can host the runtime.",
        icon: "shippingbox"
    ) {
        ContainerLabView()
    }
}
