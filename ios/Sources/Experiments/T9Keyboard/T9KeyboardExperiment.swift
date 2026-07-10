import SwiftUI

enum T9KeyboardExperiment {
    static let experiment = Experiment(
        id: "t9-keyboard",
        title: "T9 Keyboard",
        summary: "Old Nokia-style multi-tap keypad — in-app only, same Bundle ID.",
        icon: "phone.bubble"
    ) {
        T9KeyboardDemoView()
    }
}
