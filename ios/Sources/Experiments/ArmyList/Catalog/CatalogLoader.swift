import Foundation

/// Loads the bundled Army List construction catalog.
enum CatalogLoader {
    enum LoadError: Error, Equatable, LocalizedError {
        case missingResource
        case decodeFailed(String)

        var errorDescription: String? {
            switch self {
            case .missingResource:
                return "Army List catalog.json is missing from the app bundle."
            case .decodeFailed(let detail):
                return "Army List catalog.json could not be decoded: \(detail)"
            }
        }
    }

    /// Loads from the app / test bundle. Falls back to the module resource URL used in tests.
    static func load(bundle: Bundle = .main) throws -> ArmyCatalog {
        if let url = bundle.url(forResource: "catalog", withExtension: "json", subdirectory: nil)
            ?? bundle.url(forResource: "catalog", withExtension: "json", subdirectory: "Resources")
            ?? bundle.url(forResource: "catalog", withExtension: "json", subdirectory: "Catalog/Resources")
        {
            return try decode(data: Data(contentsOf: url))
        }
        // XcodeGen may flatten the Resources folder; also try any catalog.json in the bundle.
        if let urls = bundle.urls(forResourcesWithExtension: "json", subdirectory: nil) {
            if let url = urls.first(where: { $0.lastPathComponent == "catalog.json" }) {
                return try decode(data: Data(contentsOf: url))
            }
        }
        throw LoadError.missingResource
    }

    static func decode(data: Data) throws -> ArmyCatalog {
        do {
            let decoder = JSONDecoder()
            return try decoder.decode(ArmyCatalog.self, from: data)
        } catch {
            throw LoadError.decodeFailed(String(describing: error))
        }
    }

    /// Loads from an explicit file URL (unit tests / import script output).
    static func load(from url: URL) throws -> ArmyCatalog {
        try decode(data: Data(contentsOf: url))
    }
}
