import XCTest
@testable import Playground

final class CloudDocumentMergeTests: XCTestCase {
    func testReplaceLocalWhenRemoteNewer() {
        let local = Date(timeIntervalSince1970: 100)
        let remote = Date(timeIntervalSince1970: 200)
        XCTAssertTrue(
            CloudDocumentMerge.shouldReplaceLocal(localUpdatedAt: local, remoteUpdatedAt: remote)
        )
        XCTAssertFalse(
            CloudDocumentMerge.shouldReplaceLocal(localUpdatedAt: remote, remoteUpdatedAt: local)
        )
        XCTAssertFalse(
            CloudDocumentMerge.shouldReplaceLocal(localUpdatedAt: remote, remoteUpdatedAt: remote)
        )
        XCTAssertTrue(
            CloudDocumentMerge.shouldReplaceLocal(localUpdatedAt: nil, remoteUpdatedAt: remote)
        )
    }

    func testLocalIDsToRemoveOnlyPreviouslySyncedMissingRemotely() {
        let a = UUID()
        let b = UUID()
        let c = UUID()
        let local: Set<UUID> = [a, b, c]
        let remote: Set<UUID> = [a]
        let previously: Set<UUID> = [a, b]
        let remove = CloudDocumentMerge.localIDsToRemove(
            localIDs: local,
            remoteIDs: remote,
            previouslySyncedIDs: previously
        )
        XCTAssertEqual(remove, [b])
    }
}
