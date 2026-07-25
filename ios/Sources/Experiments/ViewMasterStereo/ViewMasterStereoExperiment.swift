import SwiftUI

/// Registration entry for the View-Master stereo camera experiment.
enum ViewMasterStereoExperiment {
    static let experiment = Experiment(
        id: "view-master-stereo",
        title: "View-Master Stereo",
        summary: "Dual-wide stereo stills when landscape & level — left/right preview and wigglegram.",
        icon: "rectangle.on.rectangle.angled"
    ) {
        ViewMasterStereoView()
    }
}
