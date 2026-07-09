import SwiftUI

/// The launcher: a list of every registered experiment. Tapping a row pushes
/// that experiment's view. This is the home screen of the Playground app.
struct RootView: View {
    var body: some View {
        NavigationStack {
            List(ExperimentCatalog.all) { experiment in
                NavigationLink {
                    experiment.destination
                        .navigationTitle(experiment.title)
                        .navigationBarTitleDisplayMode(.inline)
                } label: {
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
        }
    }
}

#Preview {
    RootView()
}
