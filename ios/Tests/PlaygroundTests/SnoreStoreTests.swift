import XCTest
@testable import Playground

final class SnoreStoreTests: XCTestCase {
    private var tempDir: URL!
    private var store: SnoreStore!

    override func setUpWithError() throws {
        tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent("snore-store-tests-\(UUID().uuidString)", isDirectory: true)
        store = SnoreStore(directory: tempDir)
    }

    override func tearDownWithError() throws {
        try? FileManager.default.removeItem(at: tempDir)
    }

    private func makeSession(startedAt: Date = Date(), eventCount: Int = 1) -> SleepSession {
        let id = UUID()
        var events: [SnoreEvent] = []
        for i in 0..<eventCount {
            let eventID = UUID()
            events.append(
                SnoreEvent(
                    id: eventID,
                    startedAt: startedAt.addingTimeInterval(Double(i) * 60),
                    sessionOffset: Double(i) * 60,
                    durationSeconds: 1.5,
                    peakRMS: 0.12,
                    noiseFloorAtOnset: 0.01,
                    clipFileName: "clip-\(eventID.uuidString).caf"
                )
            )
        }
        return SleepSession(
            id: id,
            startedAt: startedAt,
            endedAt: startedAt.addingTimeInterval(3_600),
            durationSeconds: 3_600,
            events: events
        )
    }

    func testPrepareSaveLoadRoundTrip() throws {
        var session = makeSession(eventCount: 2)
        try store.prepareSession(session)

        // Write a fake clip file so the path layout is exercised.
        let clipURL = store.clipURL(sessionID: session.id, fileName: session.events[0].clipFileName)
        try Data([0, 1, 2, 3]).write(to: clipURL)

        session.snoreCount = session.events.count
        try store.save(session)

        let loaded = store.loadAll()
        XCTAssertEqual(loaded.count, 1)
        let s = try XCTUnwrap(loaded.first)
        XCTAssertEqual(s.id, session.id)
        XCTAssertEqual(s.snoreCount, 2)
        XCTAssertEqual(s.events.count, 2)
        XCTAssertEqual(s.events[0].peakRMS, 0.12, accuracy: 0.0001)
        XCTAssertTrue(FileManager.default.fileExists(atPath: clipURL.path))
    }

    func testLoadAllSortsNewestFirst() throws {
        let older = makeSession(startedAt: Date(timeIntervalSince1970: 1_000))
        let newer = makeSession(startedAt: Date(timeIntervalSince1970: 2_000))
        try store.prepareSession(older)
        try store.prepareSession(newer)

        let loaded = store.loadAll()
        XCTAssertEqual(loaded.map(\.id), [newer.id, older.id])
    }

    func testDeleteRemovesFolder() throws {
        let session = makeSession()
        try store.prepareSession(session)
        XCTAssertEqual(store.loadAll().count, 1)
        try store.delete(session)
        XCTAssertEqual(store.loadAll().count, 0)
        XCTAssertFalse(FileManager.default.fileExists(atPath: store.sessionDirectory(for: session.id).path))
    }
}
