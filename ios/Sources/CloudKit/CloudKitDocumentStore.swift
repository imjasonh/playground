import CloudKit
import Foundation

/// Private-DB CloudKit store for Codable JSON documents keyed by UUID.
actor CloudKitDocumentStore {
    let recordType: String
    /// UserDefaults key for UUIDs last known on the server (deletion tracking).
    let syncedIDsKey: String
    private let database: CKDatabase
    private let defaults: UserDefaults
    /// Prefer CKAsset when payload is at least this large (rides).
    private let assetThresholdBytes: Int

    init(
        recordType: String,
        syncedIDsKey: String,
        database: CKDatabase = PlaygroundCloudKit.privateDatabase,
        defaults: UserDefaults = .standard,
        assetThresholdBytes: Int = 200_000
    ) {
        self.recordType = recordType
        self.syncedIDsKey = syncedIDsKey
        self.database = database
        self.defaults = defaults
        self.assetThresholdBytes = max(0, assetThresholdBytes)
    }

    func accountAvailable() async -> Result<Void, String> {
        do {
            let status = try await PlaygroundCloudKit.container.accountStatus()
            switch status {
            case .available:
                return .success(())
            case .noAccount:
                return .failure("Sign in to iCloud in Settings")
            case .restricted:
                return .failure("iCloud is restricted on this device")
            case .couldNotDetermine:
                return .failure("Could not reach iCloud")
            case .temporarilyUnavailable:
                return .failure("iCloud temporarily unavailable")
            @unknown default:
                return .failure("iCloud unavailable")
            }
        } catch {
            return .failure(error.localizedDescription)
        }
    }

    func fetchAll() async throws -> [CloudDocumentSnapshot] {
        let query = CKQuery(recordType: recordType, predicate: NSPredicate(value: true))
        query.sortDescriptors = [NSSortDescriptor(key: "updatedAt", ascending: false)]
        var snapshots: [CloudDocumentSnapshot] = []
        var cursor: CKQueryOperation.Cursor?
        repeat {
            let page: (matchResults: [(CKRecord.ID, Result<CKRecord, Error>)], queryCursor: CKQueryOperation.Cursor?)
            if let cursor {
                page = try await database.records(continuingMatchFrom: cursor, resultsLimit: 100)
            } else {
                page = try await database.records(
                    matching: query,
                    inZoneWith: nil,
                    desiredKeys: nil,
                    resultsLimit: 100
                )
            }
            for (_, result) in page.matchResults {
                if let record = try? result.get(),
                   let snapshot = Self.snapshot(from: record)
                {
                    snapshots.append(snapshot)
                }
            }
            cursor = page.queryCursor
        } while cursor != nil
        return snapshots
    }

    func upsert(_ snapshot: CloudDocumentSnapshot) async throws {
        let recordID = CKRecord.ID(recordName: snapshot.id.uuidString)
        let record: CKRecord
        if let existing = try? await database.record(for: recordID) {
            record = existing
        } else {
            record = CKRecord(recordType: recordType, recordID: recordID)
        }
        record["updatedAt"] = snapshot.updatedAt as CKRecordValue
        try Self.applyPayload(snapshot.payload, to: record, assetThresholdBytes: assetThresholdBytes)
        _ = try await database.save(record)
        rememberSynced(id: snapshot.id)
    }

    func delete(id: UUID) async throws {
        let recordID = CKRecord.ID(recordName: id.uuidString)
        do {
            _ = try await database.deleteRecord(withID: recordID)
        } catch let error as CKError where error.code == .unknownItem {
            // Already gone.
        }
        forgetSynced(id: id)
    }

    func previouslySyncedIDs() -> Set<UUID> {
        let raw = defaults.stringArray(forKey: syncedIDsKey) ?? []
        return Set(raw.compactMap(UUID.init(uuidString:)))
    }

    func replaceSyncedIDs(_ ids: Set<UUID>) {
        defaults.set(ids.map(\.uuidString).sorted(), forKey: syncedIDsKey)
    }

    private func rememberSynced(id: UUID) {
        var ids = previouslySyncedIDs()
        ids.insert(id)
        replaceSyncedIDs(ids)
    }

    private func forgetSynced(id: UUID) {
        var ids = previouslySyncedIDs()
        ids.remove(id)
        replaceSyncedIDs(ids)
    }

    private static func snapshot(from record: CKRecord) -> CloudDocumentSnapshot? {
        guard let id = UUID(uuidString: record.recordID.recordName) else { return nil }
        let updatedAt = (record["updatedAt"] as? Date) ?? record.modificationDate ?? .distantPast
        guard let payload = payloadData(from: record) else { return nil }
        return CloudDocumentSnapshot(id: id, updatedAt: updatedAt, payload: payload)
    }

    private static func payloadData(from record: CKRecord) -> Data? {
        if let data = record["payload"] as? Data {
            return data
        }
        if let asset = record["payloadAsset"] as? CKAsset,
           let url = asset.fileURL,
           let data = try? Data(contentsOf: url)
        {
            return data
        }
        return nil
    }

    private static func applyPayload(
        _ payload: Data,
        to record: CKRecord,
        assetThresholdBytes: Int
    ) throws {
        if payload.count >= assetThresholdBytes {
            let url = FileManager.default.temporaryDirectory
                .appendingPathComponent("ck-\(record.recordID.recordName)-\(UUID().uuidString).json")
            try payload.write(to: url, options: .atomic)
            record["payloadAsset"] = CKAsset(fileURL: url)
            record["payload"] = nil
        } else {
            record["payload"] = payload as CKRecordValue
            record["payloadAsset"] = nil
        }
    }
}
