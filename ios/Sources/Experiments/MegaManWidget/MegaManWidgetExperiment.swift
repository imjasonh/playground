import SwiftUI

enum MegaManWidgetExperiment {
    static let experiment = Experiment(
        id: "megaman-widget",
        title: "Mega Man 2 Widget",
        summary: "Timer-driven walk / jump / shoot loops on the Home Screen — pick a boss.",
        icon: "square.grid.2x2.fill"
    ) {
        MegaManWidgetDemoView()
    }
}
