import Foundation

/// On-disk episodes under Application Support / Blather / <id> /.
///
/// Each episode is an `episode.json` manifest plus one `.caf` file per segment.
struct BlatherStore: Sendable {
    let root: URL

    init(root: URL) {
        self.root = root
        try? FileManager.default.createDirectory(at: root, withIntermediateDirectories: true)
    }

    static func applicationSupport() -> BlatherStore {
        let root: URL
        if let base = try? FileManager.default.url(
            for: .applicationSupportDirectory,
            in: .userDomainMask,
            appropriateFor: nil,
            create: true
        ) {
            root = base.appendingPathComponent("Blather", isDirectory: true)
        } else {
            root = FileManager.default.temporaryDirectory.appendingPathComponent("Blather", isDirectory: true)
        }
        return BlatherStore(root: root)
    }

    func episodeDirectory(_ id: UUID) -> URL {
        root.appendingPathComponent(id.uuidString, isDirectory: true)
    }

    func audioURL(episodeID: UUID, fileName: String) -> URL {
        episodeDirectory(episodeID).appendingPathComponent(fileName)
    }

    func save(_ episode: BlatherEpisode) throws {
        let directory = episodeDirectory(episode.id)
        try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        let data = try encoder.encode(episode)
        try data.write(to: directory.appendingPathComponent("episode.json"), options: .atomic)
    }

    func load(id: UUID) -> BlatherEpisode? {
        let url = episodeDirectory(id).appendingPathComponent("episode.json")
        guard let data = try? Data(contentsOf: url) else { return nil }
        return try? JSONDecoder().decode(BlatherEpisode.self, from: data)
    }

    func summaries() -> [BlatherEpisodeSummary] {
        guard let urls = try? FileManager.default.contentsOfDirectory(
            at: root,
            includingPropertiesForKeys: nil
        ) else {
            return []
        }
        return urls.compactMap { url in
            guard let id = UUID(uuidString: url.lastPathComponent),
                  let episode = load(id: id) else {
                return nil
            }
            return BlatherEpisodeSummary(
                id: episode.id,
                topic: episode.topic,
                updatedAt: episode.updatedAt,
                duration: BlatherTimeline.duration(of: episode.segments)
            )
        }
        .sorted { $0.updatedAt > $1.updatedAt }
    }

    func removeAudio(episodeID: UUID, fileName: String) {
        try? FileManager.default.removeItem(at: audioURL(episodeID: episodeID, fileName: fileName))
    }

    func delete(id: UUID) {
        try? FileManager.default.removeItem(at: episodeDirectory(id))
    }
}
