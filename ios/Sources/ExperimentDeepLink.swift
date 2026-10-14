import Foundation

/// `playground://experiment/<id>` URLs that open an experiment from the launcher.
enum ExperimentDeepLink {
    static let scheme = "playground"
    static let host = "experiment"

    static func url(forExperimentID id: String) -> URL? {
        guard !id.isEmpty else { return nil }
        var components = URLComponents()
        components.scheme = scheme
        components.host = host
        components.path = "/\(id)"
        return components.url
    }

    static func experimentID(from url: URL) -> String? {
        guard url.scheme == scheme, url.host == host else { return nil }
        let trimmed = url.path.trimmingCharacters(in: CharacterSet(charactersIn: "/"))
        return trimmed.isEmpty ? nil : trimmed
    }
}
