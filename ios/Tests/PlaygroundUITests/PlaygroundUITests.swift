import XCTest

/// Smoke-level UI tests that drive the launcher and its experiments through the
/// accessibility identifiers declared in the views.
final class PlaygroundUITests: XCTestCase {
    override func setUp() {
        super.setUp()
        continueAfterFailure = false
    }

    override func tearDown() {
        // Leave a clean process for the next test — reduces "Lost connection to
        // the application" flakes when a prior experiment kept location/audio alive.
        XCUIApplication().terminate()
        super.tearDown()
    }

    /// Tap an experiment's launcher row, tolerating whether SwiftUI exposes the
    /// row as a button/cell (by identifier) or only its title text.
    private func openExperiment(_ id: String, title: String, in app: XCUIApplication) {
        let byId = app.buttons["experiment-\(id)"]
        if byId.waitForExistence(timeout: 8) {
            byId.tap()
            return
        }
        let byTitle = app.staticTexts[title]
        XCTAssertTrue(byTitle.waitForExistence(timeout: 8), "Could not find launcher row for \(id)")
        byTitle.tap()
    }

    private func launchApp() -> XCUIApplication {
        let app = XCUIApplication()
        app.launch()
        XCTAssertTrue(app.navigationBars["Playground"].waitForExistence(timeout: 10))
        return app
    }

    func testLauncherListsExperiments() {
        let app = launchApp()

        XCTAssertTrue(app.staticTexts["Ride Monitor"].exists)
        XCTAssertTrue(app.staticTexts["T9 Keyboard"].exists)
        XCTAssertTrue(app.staticTexts["Follow the Hum"].exists)
        XCTAssertTrue(app.staticTexts["Snore Log"].exists)
        XCTAssertTrue(app.staticTexts["Z-Camera"].exists)
        XCTAssertTrue(app.staticTexts["Voxel World"].exists)
    }

    func testRideMonitorExperimentOpens() {
        let app = launchApp()

        openExperiment("ride-monitor", title: "Ride Monitor", in: app)

        XCTAssertTrue(app.buttons["startRideButton"].waitForExistence(timeout: 8))
    }

    func testT9KeyboardExperimentOpens() {
        let app = launchApp()

        openExperiment("t9-keyboard", title: "T9 Keyboard", in: app)

        // Smoke-test that the experiment pushed; multi-tap logic is covered by
        // T9MultiTapEngineTests unit tests. Avoid depending on how SwiftUI
        // exposes individual pad keys in the accessibility tree.
        XCTAssertTrue(app.navigationBars["T9 Keyboard"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.staticTexts["Try it here"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["t9OpenSettingsButton"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["t9DemoDeleteButton"].waitForExistence(timeout: 8))
    }

    func testFollowTheHumExperimentOpens() {
        let app = launchApp()

        openExperiment("follow-the-hum", title: "Follow the Hum", in: app)

        // Prefer stable controls over the nav title — title matching has been
        // flaky when the simulator briefly loses the XCTest connection.
        XCTAssertTrue(
            app.buttons["startHumHuntButton"].waitForExistence(timeout: 10)
                || app.navigationBars["Follow the Hum"].waitForExistence(timeout: 5),
            "Follow the Hum did not open"
        )
        XCTAssertTrue(app.buttons["startHumHuntButton"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.otherElements["humStatusMessage"].waitForExistence(timeout: 8)
            || app.staticTexts["humStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["Put on AirPods, then start a hunt."].waitForExistence(timeout: 3))
    }

    func testSnoreLogExperimentOpens() {
        let app = launchApp()

        openExperiment("snore-log", title: "Snore Log", in: app)

        XCTAssertTrue(app.navigationBars["Snore Log"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["startSnoreSessionButton"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["pastSnoreSessionsButton"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.sliders["snoreSensitivitySlider"].waitForExistence(timeout: 8)
            || app.otherElements["snoreSensitivitySlider"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["snoreStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["snoreStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["Ready"].waitForExistence(timeout: 3))
    }

    func testZCameraExperimentOpens() {
        let app = launchApp()

        openExperiment("z-camera", title: "Z-Camera", in: app)

        XCTAssertTrue(app.navigationBars["Z-Camera"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.sliders["zCameraNearSlider"].waitForExistence(timeout: 8)
            || app.otherElements["zCameraNearSlider"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.sliders["zCameraFarSlider"].waitForExistence(timeout: 8)
            || app.otherElements["zCameraFarSlider"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.buttons["zCameraDepthOverlayCheckbox"].waitForExistence(timeout: 8)
            || app.otherElements["zCameraDepthOverlayCheckbox"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["zCameraStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["zCameraStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["zCameraBandSummary"].waitForExistence(timeout: 3))
    }

    func testVoxelWorldExperimentOpens() {
        let app = launchApp()

        openExperiment("voxel-world", title: "Voxel World", in: app)

        XCTAssertTrue(app.navigationBars["Voxel World"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.sliders["voxelSizeSlider"].waitForExistence(timeout: 8)
            || app.otherElements["voxelSizeSlider"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.buttons["voxelResetButton"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["voxelFreezeCheckbox"].waitForExistence(timeout: 8)
            || app.otherElements["voxelFreezeCheckbox"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["voxelStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["voxelStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["voxelSizeLabel"].waitForExistence(timeout: 3))
    }
}
