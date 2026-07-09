import XCTest
@testable import Playground

final class RideStoreTests: XCTestCase {
    private var tempDir: URL!
    private var store: RideStore!

    override func setUpWithError() throws {
        tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent("ride-store-tests-\(UUID().uuidString)", isDirectory: true)
        store = RideStore(directory: tempDir)
    }

    override func tearDownWithError() throws {
        try? FileManager.default.removeItem(at: tempDir)
    }

    private func makeRide(startedAt: Date = Date(), crashCount: Int = 0) -> Ride {
        Ride(
            id: UUID(),
            startedAt: startedAt,
            endedAt: startedAt.addingTimeInterval(600),
            durationSeconds: 600,
            distanceMeters: 4200,
            peakG: 3.7,
            joltCount: 5,
            crashCount: crashCount,
            events: [
                RideEvent(severity: .pothole, peakG: 1.6, at: 12, latitude: 40.1, longitude: -74.2),
                RideEvent(severity: .crash, peakG: 5.1, at: 300, latitude: 40.2, longitude: -74.3)
            ],
            track: [
                LocationSample(t: 0, latitude: 40.1, longitude: -74.2, altitude: 10,
                               horizontalAccuracy: 5, verticalAccuracy: 8, speed: 4.2, course: 90)
            ],
            motion: [MotionSummary(t: 0, peakG: 1.6, meanG: 0.3, peakRotation: 0.5, samples: 50)],
            barometer: [AltitudeSample(t: 0, relativeAltitude: 0, pressureKPa: 101.2)]
        )
    }

    func testSaveThenLoadRoundTrips() throws {
        let ride = makeRide()
        try store.save(ride)

        let loaded = store.loadAll()
        XCTAssertEqual(loaded.count, 1)
        let r = try XCTUnwrap(loaded.first)
        XCTAssertEqual(r.id, ride.id)
        XCTAssertEqual(r.distanceMeters, 4200, accuracy: 0.001)
        XCTAssertEqual(r.events.count, 2)
        XCTAssertEqual(r.events.last?.severity, .crash)
        XCTAssertEqual(r.track.count, 1)
        XCTAssertEqual(r.motion.first?.samples, 50)
        XCTAssertEqual(r.barometer.first?.pressureKPa ?? 0, 101.2, accuracy: 0.001)
    }

    func testLoadAllSortsNewestFirst() throws {
        let older = makeRide(startedAt: Date(timeIntervalSince1970: 1_000))
        let newer = makeRide(startedAt: Date(timeIntervalSince1970: 2_000))
        try store.save(older)
        try store.save(newer)

        let loaded = store.loadAll()
        XCTAssertEqual(loaded.map(\.id), [newer.id, older.id])
    }

    func testDeleteRemovesRide() throws {
        let ride = makeRide()
        try store.save(ride)
        XCTAssertEqual(store.loadAll().count, 1)

        try store.delete(ride)
        XCTAssertTrue(store.loadAll().isEmpty)
    }

    func testLoadAllOnEmptyDirectoryReturnsEmpty() {
        XCTAssertTrue(store.loadAll().isEmpty)
    }
}
