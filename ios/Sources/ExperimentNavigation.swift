import Foundation

/// Host navigation path so a Live Activity tap can push an experiment.
@MainActor
final class ExperimentNavigation: ObservableObject {
    @Published var path: [String] = []

    func openExperiment(id: String) {
        path = [id]
    }
}
