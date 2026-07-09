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

/// The registry of every experiment in the app. **To add an experiment:** create
/// its SwiftUI view under `Sources/Experiments/`, then add one entry here. Keep
/// `id`s stable and unique (they double as UI-test accessibility identifiers).
enum ExperimentCatalog {
    static let all: [Experiment] = [
        Experiment(
            id: "temperature-converter",
            title: "Temperature Converter",
            summary: "Convert between Celsius and Fahrenheit.",
            icon: "thermometer.medium"
        ) {
            TemperatureConverterView()
        },
        Experiment(
            id: "counter",
            title: "Counter",
            summary: "A simple bounded tap counter.",
            icon: "plusminus.circle"
        ) {
            CounterView()
        }
    ]
}
