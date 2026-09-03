import SwiftUI

/// Registration entry for the Army List experiment.
enum ArmyListExperiment {
    static let experiment = Experiment(
        id: "army-list",
        title: "Army List",
        summary: "Build and validate Warhammer 40,000 11th Edition army lists across every Munitorum Field Manual faction.",
        icon: "shield.lefthalf.filled"
    ) {
        ArmyListHomeView()
    }
}
