import Foundation

/// URL scheme the host app and Live Activities share so a tap on the island
/// can open a specific experiment.
enum ExperimentDeepLink {
    static let scheme = "playground"
    static let host = "experiment"

    /// `playground://experiment/<id>`, or `nil` if `id` cannot form a URL.
    static func url(forExperimentID id: String) -> URL? {
        guard !id.isEmpty else { return nil }
        var components = URLComponents()
        components.scheme = scheme
        components.host = host
        components.path = "/\(id)"
        return components.url
    }

    /// Experiment catalog id from a `playground://experiment/<id>` URL.
    static func experimentID(from url: URL) -> String? {
        guard url.scheme == scheme, url.host == host else { return nil }
        let trimmed = url.path.trimmingCharacters(in: CharacterSet(charactersIn: "/"))
        return trimmed.isEmpty ? nil : trimmed
    }
}
