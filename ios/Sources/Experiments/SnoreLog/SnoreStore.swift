import Foundation

/// Persists sleep sessions as JSON plus per-event CAF clips on disk.
///
/// Layout under `directory` (defaults to Documents/snore-sessions):
/// ```
/// <session-id>/
///   session.json
///   clips/
///     clip-<event-id>.caf
/// ```
struct SnoreStore {
    let directory: URL

    init(directory: URL? = nil) {
        if let directory {
            self.directory = directory
        } else {
            let documents = FileManager.default.urls(for: .documentDirectory, in: .userDomainMask)[0]
            self.directory = documents.appendingPathComponent("snore-sessions", isDirectory: true)
        }
    }

    func sessionDirectory(for id: UUID) -> URL {
        directory.appendingPathComponent(id.uuidString, isDirectory: true)
    }

    func clipsDirectory(for id: UUID) -> URL {
        sessionDirectory(for: id).appendingPathComponent("clips", isDirectory: true)
    }

    func clipURL(sessionID: UUID, fileName: String) -> URL {
        clipsDirectory(for: sessionID).appendingPathComponent(fileName)
    }

    private static func makeEncoder() -> JSONEncoder {
        let encoder = JSONEncoder()
        encoder.dateEncodingStrategy = .iso8601
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        return encoder
    }

    private static func makeDecoder() -> JSONDecoder {
        let decoder = JSONDecoder()
        decoder.dateDecodingStrategy = .iso8601
        return decoder
    }

    /// Creates the session folder (and empty clips dir) up front so clips can be
    /// written as events fire during a live session.
    func prepareSession(_ session: SleepSession) throws {
        let clips = clipsDirectory(for: session.id)
        try FileManager.default.createDirectory(at: clips, withIntermediateDirectories: true)
        try save(session)
    }

    func save(_ session: SleepSession) throws {
        var copy = session
        copy.snoreCount = copy.events.count
        let dir = sessionDirectory(for: copy.id)
        try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        let url = dir.appendingPathComponent("session.json")
        let data = try Self.makeEncoder().encode(copy)
        try data.write(to: url, options: .atomic)
    }

    /// All saved sessions, newest first. Unreadable folders are skipped.
    func loadAll() -> [SleepSession] {
        let decoder = Self.makeDecoder()
        let urls = (try? FileManager.default.contentsOfDirectory(
            at: directory,
            includingPropertiesForKeys: [.isDirectoryKey],
            options: [.skipsHiddenFiles]
        )) ?? []
        return urls.compactMap { folder -> SleepSession? in
            var isDir: ObjCBool = false
            guard FileManager.default.fileExists(atPath: folder.path, isDirectory: &isDir), isDir.boolValue else {
                return nil
            }
            let json = folder.appendingPathComponent("session.json")
            guard let data = try? Data(contentsOf: json) else { return nil }
            return try? decoder.decode(SleepSession.self, from: data)
        }
        .sorted { $0.startedAt > $1.startedAt }
    }

    func delete(_ session: SleepSession) throws {
        let dir = sessionDirectory(for: session.id)
        if FileManager.default.fileExists(atPath: dir.path) {
            try FileManager.default.removeItem(at: dir)
        }
    }
}
