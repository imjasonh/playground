import CloudKit
import Foundation

/// Shared private CloudKit container for Playground document backups.
enum PlaygroundCloudKit {
    static let containerIdentifier = "iCloud.io.github.imjasonh.playground"
    static let armyListRecordType = "ArmyListDocument"
    static let rideRecordType = "RideDocument"

    static var container: CKContainer {
        CKContainer(identifier: containerIdentifier)
    }

    static var privateDatabase: CKDatabase {
        container.privateCloudDatabase
    }
}

/// One JSON document mirrored between disk and CloudKit.
struct CloudDocumentSnapshot: Equatable, Sendable {
    var id: UUID
    var updatedAt: Date
    var payload: Data
}

enum CloudSyncStatus: Equatable, Sendable {
    case idle
    case syncing
    case unavailable(String)
    case synced(pulled: Int, pushed: Int, removed: Int)
    case failed(String)

    var title: String {
        switch self {
        case .idle:
            return "iCloud"
        case .syncing:
            return "Syncing…"
        case .unavailable:
            return "iCloud off"
        case .synced:
            return "iCloud OK"
        case .failed:
            return "iCloud error"
        }
    }

    var detail: String {
        switch self {
        case .idle:
            return "Tap to sync"
        case .syncing:
            return "Talking to iCloud"
        case .unavailable(let reason):
            return reason
        case .synced(let pulled, let pushed, let removed):
            return "↓\(pulled) ↑\(pushed)" + (removed > 0 ? " −\(removed)" : "")
        case .failed(let message):
            return message
        }
    }
}

/// Result of a local↔CloudKit merge for one record type.
struct CloudSyncResult: Equatable, Sendable {
    var pulled: Int
    var pushed: Int
    var removedLocal: Int
    var unavailableReason: String?

    static let empty = CloudSyncResult(pulled: 0, pushed: 0, removedLocal: 0, unavailableReason: nil)
}

/// Pure merge helpers (unit-tested without CloudKit).
enum CloudDocumentMerge {
    /// Prefer the side with the later `updatedAt`. Equal timestamps keep local.
    static func shouldReplaceLocal(
        localUpdatedAt: Date?,
        remoteUpdatedAt: Date
    ) -> Bool {
        guard let localUpdatedAt else { return true }
        return remoteUpdatedAt > localUpdatedAt
    }

    /// Local files that were previously synced but are gone from CloudKit should
    /// be deleted so a delete on another device sticks.
    static func localIDsToRemove(
        localIDs: Set<UUID>,
        remoteIDs: Set<UUID>,
        previouslySyncedIDs: Set<UUID>
    ) -> Set<UUID> {
        previouslySyncedIDs.intersection(localIDs).subtracting(remoteIDs)
    }
}
