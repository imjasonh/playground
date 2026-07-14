import Foundation

/// Saves and loads rides as JSON files on disk. Each ride is one file named by
/// its id under `directory` (defaults to Documents/rides). The directory is
/// injectable so it can be unit-tested against a temporary folder.
struct RideStore {
    let directory: URL

    enum StoreError: Error {
        case documentsDirectoryUnavailable
    }

    init(directory: URL? = nil) {
        if let directory {
            self.directory = directory
        } else {
            let documents = FileManager.default.urls(for: .documentDirectory, in: .userDomainMask).first
            // Fall back to temporaryDirectory rather than crash on `urls(...)[0]`
            // if Documents is somehow unavailable.
            self.directory = (documents ?? FileManager.default.temporaryDirectory)
                .appendingPathComponent("rides", isDirectory: true)
        }
    }

    private static func makeEncoder() -> JSONEncoder {
        let encoder = JSONEncoder()
        encoder.dateEncodingStrategy = .iso8601
        // Compact JSON: pretty-printing multi-hour rides on the main actor was
        // a stop-path hang, and sortedKeys adds little for machine-only files.
        return encoder
    }

    private static func makeDecoder() -> JSONDecoder {
        let decoder = JSONDecoder()
        decoder.dateDecodingStrategy = .iso8601
        return decoder
    }

    func save(_ ride: Ride) throws {
        try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
        let url = directory.appendingPathComponent("\(ride.id.uuidString).json")
        let data = try Self.makeEncoder().encode(ride)
        try data.write(to: url, options: .atomic)
    }

    /// All saved rides, newest first. Unreadable/corrupt files are skipped.
    func loadAll() -> [Ride] {
        let decoder = Self.makeDecoder()
        let urls = (try? FileManager.default.contentsOfDirectory(
            at: directory,
            includingPropertiesForKeys: nil
        )) ?? []
        return urls
            .filter { $0.pathExtension == "json" }
            .compactMap { try? decoder.decode(Ride.self, from: Data(contentsOf: $0)) }
            .sorted { $0.startedAt > $1.startedAt }
    }

    func delete(_ ride: Ride) throws {
        let url = directory.appendingPathComponent("\(ride.id.uuidString).json")
        if FileManager.default.fileExists(atPath: url.path) {
            try FileManager.default.removeItem(at: url)
        }
    }
}
