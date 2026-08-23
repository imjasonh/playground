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
    /// row as a button/cell (by identifier) or only its title text. Scrolls the
    /// list when later experiments sit below the fold on small simulators.
    private func openExperiment(_ id: String, title: String, in app: XCUIApplication) {
        let byId = app.buttons["experiment-\(id)"]
        if scrollLauncherUntilExists(byId, in: app) {
            byId.tap()
            return
        }
        let byTitle = app.staticTexts[title]
        XCTAssertTrue(
            scrollLauncherUntilExists(byTitle, in: app),
            "Could not find launcher row for \(id)"
        )
        byTitle.tap()
    }

    /// Swipe the launcher list until `element` appears (or attempts are exhausted).
    @discardableResult
    private func scrollLauncherUntilExists(
        _ element: XCUIElement,
        in app: XCUIApplication,
        maxSwipes: Int = 8
    ) -> Bool {
        if element.waitForExistence(timeout: 2) {
            return true
        }
        for _ in 0..<maxSwipes {
            if element.exists {
                return true
            }
            swipeLauncherUp(in: app)
        }
        return element.waitForExistence(timeout: 2)
    }

    private func swipeLauncherUp(in app: XCUIApplication) {
        if app.collectionViews.firstMatch.exists {
            app.collectionViews.firstMatch.swipeUp()
        } else if app.tables.firstMatch.exists {
            app.tables.firstMatch.swipeUp()
        } else {
            app.swipeUp()
        }
    }

    private func launchApp() -> XCUIApplication {
        let app = XCUIApplication()
        app.launch()
        XCTAssertTrue(app.navigationBars["Playground"].waitForExistence(timeout: 10))
        return app
    }

    func testLauncherListsExperiments() {
        let app = launchApp()

        // Early rows stay on-screen; later ones may sit below the fold once the
        // catalog grows (SwiftUI List also virtualizes off-screen cells).
        XCTAssertTrue(app.staticTexts["Ride Monitor"].exists)
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Device Agent"], in: app),
            "Device Agent should appear in the launcher"
        )
        XCTAssertTrue(app.staticTexts["T9 Keyboard"].exists)
        XCTAssertTrue(app.staticTexts["Follow the Hum"].exists)
        XCTAssertTrue(app.staticTexts["Snore Log"].exists)
        XCTAssertTrue(app.staticTexts["Z-Camera"].exists)
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Local Lens"], in: app),
            "Local Lens should appear after scrolling the launcher"
        )
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Voxel World"], in: app),
            "Voxel World should appear after scrolling the launcher"
        )
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Wigglecam"], in: app),
            "Wigglecam should appear after scrolling the launcher"
        )
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["NFC Tags"], in: app),
            "NFC Tags should appear after scrolling the launcher"
        )
    }

    func testRideMonitorExperimentOpens() {
        let app = launchApp()

        openExperiment("ride-monitor", title: "Ride Monitor", in: app)

        XCTAssertTrue(app.buttons["startRideButton"].waitForExistence(timeout: 8))
    }

    func testDeviceAgentExperimentOpens() {
        let app = launchApp()

        openExperiment("device-agent", title: "Device Agent", in: app)

        XCTAssertTrue(app.navigationBars["Device Agent"].waitForExistence(timeout: 8))
        // Simulator / CI has no Apple Intelligence model — UI must show the
        // blocked state rather than a fake keyword planner.
        let unavailable = app.otherElements["deviceAgentUnavailable"]
            .waitForExistence(timeout: 8)
            || app.staticTexts["deviceAgentUnavailableTitle"].waitForExistence(timeout: 3)
        let readyComposer = app.textFields["deviceAgentPromptField"].waitForExistence(timeout: 2)
            || app.textViews["deviceAgentPromptField"].waitForExistence(timeout: 1)
        XCTAssertTrue(
            unavailable || readyComposer,
            "Expected unavailable pane (Simulator) or composer (Apple Intelligence device)"
        )
        if unavailable {
            XCTAssertTrue(
                app.staticTexts["deviceAgentUnavailableDetail"].waitForExistence(timeout: 3)
                    || app.otherElements["deviceAgentUnavailableDetail"].waitForExistence(timeout: 2)
                    || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "Apple Intelligence")).firstMatch.exists
                    || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "iOS 26")).firstMatch.exists
                    || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "eligible")).firstMatch.exists
            )
        } else {
            XCTAssertTrue(app.buttons["deviceAgentSendButton"].waitForExistence(timeout: 8))
            XCTAssertTrue(app.buttons["deviceAgentVoiceModeButton"].waitForExistence(timeout: 8))
        }
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

    func testWigglecamExperimentOpens() {
        let app = launchApp()

        openExperiment("wigglecam", title: "Wigglecam", in: app)

        XCTAssertTrue(app.navigationBars["Wigglecam"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["wigglecamCaptureButton"].waitForExistence(timeout: 8)
            || app.otherElements["wigglecamCaptureButton"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["wigglecamStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["wigglecamStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["wigglecamReadinessBanner"].waitForExistence(timeout: 3)
            || app.otherElements["wigglecamReadinessBanner"].waitForExistence(timeout: 3))
    }

    func testLocalLensExperimentOpens() {
        let app = launchApp()

        openExperiment("local-lens", title: "Local Lens", in: app)

        XCTAssertTrue(app.navigationBars["Local Lens"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["localLensMode-classify"].waitForExistence(timeout: 8)
            || app.otherElements["localLensMode-classify"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.buttons["localLensMode-text"].waitForExistence(timeout: 8)
            || app.otherElements["localLensMode-text"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.buttons["localLensMode-body"].waitForExistence(timeout: 8)
            || app.otherElements["localLensMode-body"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.buttons["localLensMode-hands"].waitForExistence(timeout: 8)
            || app.otherElements["localLensMode-hands"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["localLensStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["localLensStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["localLensPrivacyBadge"].waitForExistence(timeout: 3)
            || app.otherElements["localLensPrivacyBadge"].waitForExistence(timeout: 3))
    }

    func testNFCTagsExperimentOpens() {
        let app = launchApp()

        openExperiment("nfc-tags", title: "NFC Tags", in: app)

        XCTAssertTrue(app.navigationBars["NFC Tags"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["nfcScanButton"].waitForExistence(timeout: 8)
            || app.otherElements["nfcScanButton"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["nfcStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["nfcStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["Hold an NFC tag near the top of the iPhone."].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["nfcAvailabilityBanner"].waitForExistence(timeout: 8)
            || app.otherElements["nfcAvailabilityBanner"].waitForExistence(timeout: 3)
            || app.staticTexts["NFC reader ready"].waitForExistence(timeout: 3)
            || app.staticTexts["NFC needs a physical iPhone. The Simulator cannot scan tags."].waitForExistence(timeout: 3))
    }
}
