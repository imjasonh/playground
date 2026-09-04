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
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Army List"], in: app),
            "Army List should appear after scrolling the launcher"
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

        // CI’s iOS 26 Simulator may report Foundation Models available; older
        // hosts show the unavailable pane. Match any marker in one wait so the
        // available path isn’t starved by a long unavailable timeout.
        let unavailable = app.descendants(matching: .any)["deviceAgentUnavailable"]
        let unavailableTitle = app.descendants(matching: .any)["deviceAgentUnavailableTitle"]
        let composer = app.descendants(matching: .any)["deviceAgentComposer"]
        let prompt = app.descendants(matching: .any)["deviceAgentPromptField"]
        let send = app.buttons["deviceAgentSendButton"]
        let voice = app.buttons["deviceAgentVoiceModeButton"]
        let modelStatus = app.descendants(matching: .any)["deviceAgentModelStatus"]
        let root = app.descendants(matching: .any)["deviceAgentRoot"]

        let marker = NSPredicate { _, _ in
            unavailable.exists
                || unavailableTitle.exists
                || composer.exists
                || prompt.exists
                || send.exists
                || modelStatus.exists
                || root.exists
        }
        let ready = XCTNSPredicateExpectation(predicate: marker, object: app)
        let waited = XCTWaiter.wait(for: [ready], timeout: 12)
        XCTAssertEqual(waited, .completed, "Expected unavailable pane or Device Agent chat UI")

        if unavailable.exists || unavailableTitle.exists {
            XCTAssertTrue(
                app.descendants(matching: .any)["deviceAgentUnavailableDetail"].waitForExistence(timeout: 3)
                    || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "Apple Intelligence")).firstMatch.exists
                    || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "iOS 26")).firstMatch.exists
                    || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "Foundation")).firstMatch.exists
            )
        } else {
            XCTAssertTrue(
                send.waitForExistence(timeout: 8) || voice.waitForExistence(timeout: 2) || prompt.exists || composer.exists,
                "Expected composer controls when the model gate is available"
            )
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

    func testArmyListExperimentOpens() {
        let app = launchApp()

        openExperiment("army-list", title: "Army List", in: app)

        XCTAssertTrue(app.navigationBars["Army List"].waitForExistence(timeout: 8))

        // While catalog bootstrap runs, Create must stay disabled (or absent).
        let loading = app.descendants(matching: .any)["armyListCatalogLoading"]
        if loading.exists {
            let newButton = app.buttons["armyListNewButton"]
            if newButton.exists {
                XCTAssertFalse(
                    newButton.isEnabled,
                    "New list must stay disabled while the catalog is loading"
                )
            }
        }

        let unavailable = app.descendants(matching: .any)["armyListCatalogUnavailable"]
        let empty = app.descendants(matching: .any)["armyListEmptyState"]
        let library = app.descendants(matching: .any)["armyListLibrary"]
        let marker = NSPredicate { _, _ in
            unavailable.exists || empty.exists || library.exists
        }
        let ready = XCTNSPredicateExpectation(predicate: marker, object: app)
        XCTAssertEqual(
            XCTWaiter.wait(for: [ready], timeout: 10),
            .completed,
            "Expected catalog-unavailable, empty state, or library after bootstrap"
        )
    }

    func testArmyListNewListOpensEditorOrShowsError() {
        let app = launchApp()

        openExperiment("army-list", title: "Army List", in: app)
        XCTAssertTrue(app.navigationBars["Army List"].waitForExistence(timeout: 8))
        waitForArmyListBootstrap(in: app)

        let unavailable = app.descendants(matching: .any)["armyListCatalogUnavailable"]
        if unavailable.exists {
            // Catalog missing from the bundle: New list must stay disabled so we
            // never present a blank sheet again.
            let newButton = app.buttons["armyListNewButton"]
            if newButton.exists {
                XCTAssertFalse(newButton.isEnabled, "New list must stay disabled when the catalog is missing")
            }
            XCTAssertTrue(
                app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "catalog.json")).firstMatch.exists
                    || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "missing")).firstMatch.exists
                    || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "Catalog unavailable")).firstMatch.exists
            )
            return
        }

        let newButton = app.buttons["armyListNewButton"]
        XCTAssertTrue(newButton.waitForExistence(timeout: 8), "New list control missing")
        XCTAssertTrue(newButton.isEnabled, "New list should be enabled when the catalog loaded")
        newButton.tap()

        let nameField = app.descendants(matching: .any)["armyListNameField"]
        let sheetUnavailable = app.descendants(matching: .any)["armyListNewSheetUnavailable"]
        let sheetReady = NSPredicate { _, _ in
            nameField.exists || sheetUnavailable.exists
        }
        let sheetExpectation = XCTNSPredicateExpectation(predicate: sheetReady, object: app)
        XCTAssertEqual(
            XCTWaiter.wait(for: [sheetExpectation], timeout: 8),
            .completed,
            "New list sheet was blank — expected the create form or an explicit error"
        )

        if sheetUnavailable.exists {
            XCTAssertTrue(app.buttons["armyListNewSheetCancel"].waitForExistence(timeout: 3))
            return
        }

        XCTAssertTrue(nameField.waitForExistence(timeout: 3))
        nameField.tap()
        // Clear the default title, then type a unique name.
        if let value = nameField.value as? String, !value.isEmpty {
            let delete = String(repeating: XCUIKeyboardKey.delete.rawValue, count: value.count)
            nameField.typeText(delete)
        }
        let listName = "UI Test \(Int(Date().timeIntervalSince1970))"
        nameField.typeText(listName)

        let create = app.buttons["armyListCreateButton"]
        XCTAssertTrue(create.waitForExistence(timeout: 3))
        XCTAssertTrue(create.isEnabled)
        create.tap()

        let legalBadge = app.descendants(matching: .any)["armyListLegalBadge"]
        let validationBanner = app.descendants(matching: .any)["armyListValidationBanner"]
        let editorUnavailable = app.descendants(matching: .any)["armyListEditorUnavailable"]
        let editorReady = NSPredicate { _, _ in
            legalBadge.exists || validationBanner.exists || editorUnavailable.exists
        }
        let editorExpectation = XCTNSPredicateExpectation(predicate: editorReady, object: app)
        XCTAssertEqual(
            XCTWaiter.wait(for: [editorExpectation], timeout: 10),
            .completed,
            "Create did not open the editor or an explicit error"
        )

        if editorUnavailable.exists {
            return
        }

        XCTAssertTrue(
            legalBadge.waitForExistence(timeout: 3) || validationBanner.exists,
            "Editor should show live validation for the new empty list"
        )
        // Brand-new lists are empty → illegal until detachments/units/warlord are set.
        XCTAssertTrue(
            app.staticTexts["Illegal"].waitForExistence(timeout: 3)
                || app.staticTexts.matching(NSPredicate(format: "label CONTAINS[c] %@", "Illegal")).firstMatch.exists
        )

        // Share must open a real sheet (not blank) via item-based presentation.
        let share = app.buttons["armyListShareButton"]
        XCTAssertTrue(share.waitForExistence(timeout: 5))
        share.tap()
        let shareText = app.descendants(matching: .any)["armyListShareText"]
        let shareSheet = app.descendants(matching: .any)["armyListShareSheet"]
        let shareReady = NSPredicate { _, _ in
            shareText.exists || shareSheet.exists
                || app.navigationBars["Share"].exists
        }
        let shareExpectation = XCTNSPredicateExpectation(predicate: shareReady, object: app)
        XCTAssertEqual(
            XCTWaiter.wait(for: [shareExpectation], timeout: 8),
            .completed,
            "Share sheet was blank — expected roster text or Share chrome"
        )
    }

    func testDeviceAgentExportSheetIsNeverBlank() {
        let app = launchApp()

        openExperiment("device-agent", title: "Device Agent", in: app)
        XCTAssertTrue(app.navigationBars["Device Agent"].waitForExistence(timeout: 8))

        let export = app.buttons["deviceAgentExportButton"]
        XCTAssertTrue(
            export.waitForExistence(timeout: 10),
            "Export control should be available (chat status bar or unavailable pane)"
        )
        export.tap()

        let shareLink = app.descendants(matching: .any)["deviceAgentExportShareLink"]
        let exportSheet = app.descendants(matching: .any)["deviceAgentExportSheet"]
        let failedAlert = app.alerts["Export failed"]
        let exportReady = NSPredicate { _, _ in
            shareLink.exists
                || exportSheet.exists
                || app.navigationBars["Export conversation"].exists
                || failedAlert.exists
        }
        let expectation = XCTNSPredicateExpectation(predicate: exportReady, object: app)
        XCTAssertEqual(
            XCTWaiter.wait(for: [expectation], timeout: 10),
            .completed,
            "Export presented a blank sheet — expected Share ZIP content or an explicit failure alert"
        )
    }

    /// Wait until Army List leaves the bootstrap ProgressView.
    private func waitForArmyListBootstrap(in app: XCUIApplication, timeout: TimeInterval = 10) {
        let unavailable = app.descendants(matching: .any)["armyListCatalogUnavailable"]
        let empty = app.descendants(matching: .any)["armyListEmptyState"]
        let library = app.descendants(matching: .any)["armyListLibrary"]
        let settled = NSPredicate { _, _ in
            unavailable.exists || empty.exists || library.exists
        }
        let expectation = XCTNSPredicateExpectation(predicate: settled, object: app)
        XCTAssertEqual(
            XCTWaiter.wait(for: [expectation], timeout: timeout),
            .completed,
            "Army List never left the loading state"
        )
    }
}
