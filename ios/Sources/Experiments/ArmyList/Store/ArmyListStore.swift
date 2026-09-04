import Foundation

/// Persists army lists as one JSON file per list under Documents/army-lists,
/// and mirrors them to private CloudKit when iCloud is available.
struct ArmyListStore {
    let directory: URL
    private let cloud: CloudKitDocumentStore?

    init(directory: URL? = nil, cloudSyncEnabled: Bool = true) {
        if let directory {
            self.directory = directory
        } else {
            let documents = FileManager.default.urls(for: .documentDirectory, in: .userDomainMask)[0]
            self.directory = documents.appendingPathComponent("army-lists", isDirectory: true)
        }
        if cloudSyncEnabled {
            cloud = CloudKitDocumentStore(
                recordType: PlaygroundCloudKit.armyListRecordType,
                syncedIDsKey: "playground.cloudkit.synced.armyLists",
                assetThresholdBytes: 750_000
            )
        } else {
            cloud = nil
        }
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

    func fileURL(for id: UUID) -> URL {
        directory.appendingPathComponent("\(id.uuidString).json")
    }

    func save(_ list: ArmyListDocument) throws {
        try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
        var copy = list
        copy.touch()
        let data = try Self.makeEncoder().encode(copy)
        try data.write(to: fileURL(for: copy.id), options: .atomic)
        if let cloud {
            CloudDocumentSync.push(
                cloud: cloud,
                id: copy.id,
                updatedAt: copy.updatedAt,
                payload: data
            )
        }
    }

    func loadAll() -> [ArmyListDocument] {
        let decoder = Self.makeDecoder()
        let urls = (try? FileManager.default.contentsOfDirectory(
            at: directory,
            includingPropertiesForKeys: nil,
            options: [.skipsHiddenFiles]
        )) ?? []
        return urls.compactMap { url -> ArmyListDocument? in
            guard url.pathExtension.lowercased() == "json" else { return nil }
            guard let data = try? Data(contentsOf: url) else { return nil }
            return try? decoder.decode(ArmyListDocument.self, from: data)
        }
        .sorted { $0.updatedAt > $1.updatedAt }
    }

    func load(id: UUID) throws -> ArmyListDocument {
        let data = try Data(contentsOf: fileURL(for: id))
        return try Self.makeDecoder().decode(ArmyListDocument.self, from: data)
    }

    func delete(_ list: ArmyListDocument) throws {
        let url = fileURL(for: list.id)
        if FileManager.default.fileExists(atPath: url.path) {
            try FileManager.default.removeItem(at: url)
        }
        if let cloud {
            CloudDocumentSync.delete(cloud: cloud, id: list.id)
        }
    }

    /// Pull remote lists and push any newer local copies.
    func syncWithCloud() async -> CloudSyncResult {
        guard let cloud else {
            return CloudSyncResult(
                pulled: 0,
                pushed: 0,
                removedLocal: 0,
                unavailableReason: "Cloud sync disabled"
            )
        }
        let decoder = Self.makeDecoder()
        return await CloudDocumentSync.merge(
            cloud: cloud,
            localDirectory: directory,
            localUpdatedAt: { _, data in
                (try? decoder.decode(ArmyListDocument.self, from: data))?.updatedAt
            },
            encodeErrorHint: "Army List sync failed"
        )
    }
}
