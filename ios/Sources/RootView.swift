import SwiftUI

/// The launcher: a list of every registered experiment. Tapping a row pushes
/// that experiment's view. This is the home screen of the Playground app.
struct RootView: View {
    @EnvironmentObject private var router: PlaygroundRouter

    var body: some View {
        NavigationStack(path: $router.path) {
            List(ExperimentCatalog.all) { experiment in
                NavigationLink(value: experiment.id) {
                    Label {
                        VStack(alignment: .leading, spacing: 2) {
                            Text(experiment.title)
                                .font(.headline)
                            Text(experiment.summary)
                                .font(.subheadline)
                                .foregroundStyle(.secondary)
                        }
                    } icon: {
                        Image(systemName: experiment.icon)
                    }
                }
                .accessibilityIdentifier("experiment-\(experiment.id)")
            }
            .navigationTitle("Playground")
            .navigationDestination(for: String.self) { id in
                if let experiment = ExperimentCatalog.all.first(where: { $0.id == id }) {
                    experiment.destination
                        .navigationTitle(experiment.title)
                        .navigationBarTitleDisplayMode(.inline)
                } else {
                    Text("Unknown experiment")
                }
            }
        }
    }
}

#Preview {
    RootView()
        .environmentObject(PlaygroundRouter.shared)
}
