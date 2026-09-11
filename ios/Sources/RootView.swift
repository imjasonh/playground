import SwiftUI

/// The launcher: a list of every registered experiment. Tapping a row pushes
/// that experiment's view. This is the home screen of the Playground app.
struct RootView: View {
    @EnvironmentObject private var router: PlaygroundRouter
    @State private var searchText = ""

    private var filteredExperiments: [Experiment] {
        let query = searchText.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !query.isEmpty else { return ExperimentCatalog.all }
        return ExperimentCatalog.all.filter { experiment in
            experiment.title.localizedCaseInsensitiveContains(query)
                || experiment.summary.localizedCaseInsensitiveContains(query)
        }
    }

    var body: some View {
        NavigationStack(path: $router.path) {
            List {
                ForEach(filteredExperiments) { experiment in
                    NavigationLink(value: experiment.id) {
                        Label {
                            VStack(alignment: .leading, spacing: 3) {
                                Text(experiment.title)
                                    .font(.headline)
                                Text(experiment.summary)
                                    .font(.subheadline)
                                    .foregroundStyle(.secondary)
                                    .lineLimit(2)
                            }
                        } icon: {
                            Image(systemName: experiment.icon)
                                .symbolRenderingMode(.hierarchical)
                                .foregroundStyle(.tint)
                                .frame(width: 28, alignment: .center)
                        }
                    }
                    .accessibilityElement(children: .combine)
                    .accessibilityIdentifier("experiment-\(experiment.id)")
                }
            }
            .listStyle(.insetGrouped)
            .searchable(text: $searchText, prompt: "Search experiments")
            .overlay {
                if filteredExperiments.isEmpty {
                    ContentUnavailableView.search(text: searchText)
                }
            }
            .navigationTitle("Playground")
            .toolbarMinimizationBehavior(.onScrollDown, for: .navigationBar)
            .navigationDestination(for: String.self) { id in
                if let experiment = ExperimentCatalog.all.first(where: { $0.id == id }) {
                    experiment.destination
                        .navigationTitle(experiment.title)
                        .navigationBarTitleDisplayMode(.inline)
                } else {
                    ContentUnavailableView(
                        "Unknown experiment",
                        systemImage: "questionmark.circle",
                        description: Text("That experiment ID is not in this build.")
                    )
                }
            }
        }
    }
}

#Preview {
    RootView()
        .environmentObject(PlaygroundRouter.shared)
}
