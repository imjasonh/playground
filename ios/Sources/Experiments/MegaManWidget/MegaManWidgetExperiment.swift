import SwiftUI

enum MegaManWidgetExperiment {
    static let experiment = Experiment(
        id: "megaman-widget",
        title: "Mega Man 2 Widget",
        summary: "Metal Man walk / throw / jump loop on the Home Screen via timer-mask animation.",
        icon: "square.grid.2x2.fill"
    ) {
        MegaManWidgetDemoView()
    }
}
