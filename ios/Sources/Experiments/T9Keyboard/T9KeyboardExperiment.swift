import SwiftUI

enum T9KeyboardExperiment {
    static let experiment = Experiment(
        id: "t9-keyboard",
        title: "T9 Keyboard",
        summary: "Old Nokia-style multi-tap keypad — try it here, then enable the system keyboard.",
        icon: "phone.bubble"
    ) {
        T9KeyboardDemoView()
    }
}
