import XCTest
@testable import Playground

@MainActor
final class PhoneVRStoreTests: XCTestCase {
    /// A throwaway defaults suite that is deleted when the test ends.
    private func makeDefaults() throws -> UserDefaults {
        let suite = "phonevr.store.tests.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        addTeardownBlock { defaults.removePersistentDomain(forName: suite) }
        return defaults
    }

    private func sessionSummary() -> VRSessionSummary {
        var statistics = VRFrameStatistics()
        for frame in 0..<240 {
            statistics.recordFrame(
                presentationTime: Double(frame) / 120,
                expectedInterval: 1.0 / 120,
                cpuMilliseconds: 2.5,
                mode: frame < 200 ? .sixDoF : .threeDoF,
                thermal: frame < 100 ? .nominal : .fair,
                eyeResolution: 1024
            )
            statistics.recordGPU(eyePassMilliseconds: 4.2, finalPassMilliseconds: 0.9)
            statistics.recordPhotonLatency(milliseconds: 14)
        }
        return statistics.summary(endedAt: Date(timeIntervalSinceReferenceDate: 800_000_000), slips: 1, airPodsLatency: 0.045)
    }

    func testStartsWithDefaults() throws {
        let store = PhoneVRStore(defaults: try makeDefaults())
        XCTAssertEqual(store.settings, PhoneVRSettings())
        XCTAssertNil(store.lastSummary)
    }

    func testSettingsPersistAcrossLaunches() throws {
        let defaults = try makeDefaults()
        let store = PhoneVRStore(defaults: defaults)
        store.settings.refreshRate = .hz60
        store.settings.timewarp = false
        store.settings.profile.distortionK1 = 0.3

        let reloaded = PhoneVRStore(defaults: defaults)
        XCTAssertEqual(reloaded.settings.refreshRate, .hz60)
        XCTAssertFalse(reloaded.settings.timewarp)
        XCTAssertEqual(reloaded.settings.profile.distortionK1, 0.3)
    }

    func testRecordingASessionKeepsItsCalibrationAndMeasurements() throws {
        let defaults = try makeDefaults()
        let store = PhoneVRStore(defaults: defaults)
        var calibrated = store.settings.profile
        calibrated.interLensDistance = 0.062
        calibrated.distortionK2 = 0.2
        let summary = sessionSummary()
        XCTAssertEqual(summary.frames, 240)
        XCTAssertEqual(summary.averageFrameRate, 120, accuracy: 0.5)

        store.record(VRSessionResult(summary: summary, profile: calibrated))
        XCTAssertEqual(store.settings.profile, calibrated)
        XCTAssertEqual(store.lastSummary, summary)

        let reloaded = PhoneVRStore(defaults: defaults)
        XCTAssertEqual(reloaded.settings.profile, calibrated)
        XCTAssertEqual(reloaded.lastSummary, summary)
    }

    func testResetViewerRestoresTheStandardProfileOnly() throws {
        let defaults = try makeDefaults()
        let store = PhoneVRStore(defaults: defaults)
        store.settings.profile.screenToLensDistance = 0.05
        store.settings.mounting = .cameraRight
        store.resetViewer()

        let reloaded = PhoneVRStore(defaults: defaults)
        XCTAssertEqual(reloaded.settings.profile, .standard)
        XCTAssertEqual(reloaded.settings.mounting, .cameraRight)
    }
}
