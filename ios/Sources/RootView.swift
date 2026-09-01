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
                if filteredExperiments.isEmpty {
                    ContentUnavailableSearchRow(query: searchText)
                } else {
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
            }
            .listStyle(.insetGrouped)
            .searchable(text: $searchText, prompt: "Search experiments")
            .navigationTitle("Playground")
            .navigationDestination(for: String.self) { id in
                if let experiment = ExperimentCatalog.all.first(where: { $0.id == id }) {
                    experiment.destination
                        .navigationTitle(experiment.title)
                        .navigationBarTitleDisplayMode(.inline)
                } else {
                    VStack(spacing: 8) {
                        Image(systemName: "questionmark.circle")
                            .font(.largeTitle)
                            .foregroundStyle(.secondary)
                            .accessibilityHidden(true)
                        Text("Unknown experiment")
                            .font(.headline)
                        Text("That experiment id is not in this build.")
                            .font(.subheadline)
                            .foregroundStyle(.secondary)
                            .multilineTextAlignment(.center)
                    }
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
                    .padding()
                }
            }
        }
    }
}

/// iOS 16–friendly empty search row (no `ContentUnavailableView`).
private struct ContentUnavailableSearchRow: View {
    let query: String

    var body: some View {
        VStack(spacing: 8) {
            Image(systemName: "magnifyingglass")
                .font(.largeTitle)
                .foregroundStyle(.secondary)
                .accessibilityHidden(true)
            Text("No matches")
                .font(.headline)
            Text("Nothing matched “\(query)”.")
                .font(.subheadline)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
        }
        .frame(maxWidth: .infinity)
        .padding(.vertical, 28)
        .listRowBackground(Color.clear)
        .listRowSeparator(.hidden)
    }
}

#Preview {
    RootView()
        .environmentObject(PlaygroundRouter.shared)
}
