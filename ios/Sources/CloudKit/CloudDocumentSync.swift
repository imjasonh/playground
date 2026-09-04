import Foundation

/// Pushes/pulls local JSON document folders to private CloudKit.
enum CloudDocumentSync {
    /// Merge CloudKit into a local directory of `uuid.json` files.
    ///
    /// - Newest `updatedAt` wins when both sides have a document.
    /// - Locals never seen on the server are uploaded.
    /// - Locals previously synced but missing remotely are deleted (cross-device delete).
    static func merge(
        cloud: CloudKitDocumentStore,
        localDirectory: URL,
        localUpdatedAt: (UUID, Data) -> Date?,
        encodeErrorHint: String
    ) async -> CloudSyncResult {
        switch await cloud.accountAvailable() {
        case .failure(let reason):
            return CloudSyncResult(pulled: 0, pushed: 0, removedLocal: 0, unavailableReason: reason)
        case .success:
            break
        }

        do {
            try FileManager.default.createDirectory(at: localDirectory, withIntermediateDirectories: true)
            let remote = try await cloud.fetchAll()
            let remoteByID = Dictionary(uniqueKeysWithValues: remote.map { ($0.id, $0) })
            var localByID = try loadLocalPayloads(in: localDirectory)

            var pulled = 0
            var pushed = 0

            for (id, snapshot) in remoteByID {
                let localData = localByID[id]
                let localDate = localData.flatMap { localUpdatedAt(id, $0) }
                if CloudDocumentMerge.shouldReplaceLocal(
                    localUpdatedAt: localDate,
                    remoteUpdatedAt: snapshot.updatedAt
                ) {
                    try writeLocal(id: id, data: snapshot.payload, in: localDirectory)
                    localByID[id] = snapshot.payload
                    pulled += 1
                }
            }

            for (id, data) in localByID {
                let localDate = localUpdatedAt(id, data) ?? .distantPast
                if let remote = remoteByID[id] {
                    if localDate > remote.updatedAt {
                        try await cloud.upsert(
                            CloudDocumentSnapshot(id: id, updatedAt: localDate, payload: data)
                        )
                        pushed += 1
                    }
                } else {
                    try await cloud.upsert(
                        CloudDocumentSnapshot(id: id, updatedAt: localDate, payload: data)
                    )
                    pushed += 1
                }
            }

            let previouslySynced = await cloud.previouslySyncedIDs()
            let toRemove = CloudDocumentMerge.localIDsToRemove(
                localIDs: Set(localByID.keys),
                remoteIDs: Set(remoteByID.keys),
                previouslySyncedIDs: previouslySynced
            )
            for id in toRemove {
                try? FileManager.default.removeItem(at: fileURL(for: id, in: localDirectory))
                localByID.removeValue(forKey: id)
            }

            await cloud.replaceSyncedIDs(Set(localByID.keys).union(remoteByID.keys))
            return CloudSyncResult(
                pulled: pulled,
                pushed: pushed,
                removedLocal: toRemove.count,
                unavailableReason: nil
            )
        } catch {
            return CloudSyncResult(
                pulled: 0,
                pushed: 0,
                removedLocal: 0,
                unavailableReason: "\(encodeErrorHint): \(error.localizedDescription)"
            )
        }
    }

    static func push(
        cloud: CloudKitDocumentStore,
        id: UUID,
        updatedAt: Date,
        payload: Data
    ) {
        Task {
            if case .failure = await cloud.accountAvailable() { return }
            try? await cloud.upsert(
                CloudDocumentSnapshot(id: id, updatedAt: updatedAt, payload: payload)
            )
        }
    }

    static func delete(cloud: CloudKitDocumentStore, id: UUID) {
        Task {
            if case .failure = await cloud.accountAvailable() { return }
            try? await cloud.delete(id: id)
        }
    }

    private static func fileURL(for id: UUID, in directory: URL) -> URL {
        directory.appendingPathComponent("\(id.uuidString).json")
    }

    private static func loadLocalPayloads(in directory: URL) throws -> [UUID: Data] {
        let urls = (try? FileManager.default.contentsOfDirectory(
            at: directory,
            includingPropertiesForKeys: nil,
            options: [.skipsHiddenFiles]
        )) ?? []
        var result: [UUID: Data] = [:]
        for url in urls {
            guard url.pathExtension.lowercased() == "json" else { continue }
            let name = url.deletingPathExtension().lastPathComponent
            guard let id = UUID(uuidString: name),
                  let data = try? Data(contentsOf: url)
            else { continue }
            result[id] = data
        }
        return result
    }

    private static func writeLocal(id: UUID, data: Data, in directory: URL) throws {
        try data.write(to: fileURL(for: id, in: directory), options: .atomic)
    }
}
