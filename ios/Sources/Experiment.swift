import SwiftUI

/// A single functional experiment hosted inside the Playground app.
///
/// This is the iOS analog of "one browser app under the Pages site": the app is
/// a container, and each `Experiment` is one self-contained thing you can open
/// from the launcher. The destination view is built lazily so opening the app
/// doesn't construct every experiment up front.
struct Experiment: Identifiable {
    let id: String
    let title: String
    let summary: String
    /// SF Symbol name shown in the launcher row.
    let icon: String

    private let makeDestination: () -> AnyView

    init<Content: View>(
        id: String,
        title: String,
        summary: String,
        icon: String,
        @ViewBuilder destination: @escaping () -> Content
    ) {
        self.id = id
        self.title = title
        self.summary = summary
        self.icon = icon
        self.makeDestination = { AnyView(destination()) }
    }

    @ViewBuilder
    var destination: some View {
        makeDestination()
    }
}

/// The registry of every experiment in the app.
///
/// **To add an experiment:**
/// 1. Create `Sources/Experiments/<YourExperiment>/` (one folder per experiment).
/// 2. Add a `*Experiment.swift` in that folder that exposes a static
///    `experiment: Experiment` (id, title, summary, icon, destination view).
/// 3. Append that static to `all` below.
///
/// Keep `id`s stable and unique (they double as UI-test accessibility identifiers).
enum ExperimentCatalog {
    static let all: [Experiment] = [
        RideMonitorExperiment.experiment,
        T9KeyboardExperiment.experiment,
        FollowTheHumExperiment.experiment,
    ]
}
