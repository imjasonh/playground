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
    ///
    /// Prefers the launcher search field so late catalog rows do not depend on
    /// a long swipe chain. Falls back to scrolling. If the tap misses and the
    /// Playground list is still showing, taps once more.
    private func openExperiment(
        _ id: String,
        title: String,
        in app: XCUIApplication,
        navigationBarHidden: Bool = false
    ) {
        _ = filterLauncher(to: title, in: app)
        let byId = app.buttons["experiment-\(id)"]
        let byTitle = app.staticTexts[title]
        if !scrollLauncherUntilExists(byId, in: app) {
            XCTAssertTrue(
                scrollLauncherUntilExists(byTitle, in: app),
                "Could not find launcher row for \(id)"
            )
        }

        tapLauncherRow(id: id, title: title, in: app)
        if navigationBarHidden {
            if app.navigationBars["Playground"].waitForNonExistence(timeout: 6) {
                return
            }
            tapLauncherRow(id: id, title: title, in: app)
            XCTAssertTrue(
                app.navigationBars["Playground"].waitForNonExistence(timeout: 8),
                "Could not open experiment \(id)"
            )
            return
        }
        let destination = app.navigationBars[title]
        if destination.waitForExistence(timeout: 6) || !app.navigationBars["Playground"].exists {
            return
        }
        tapLauncherRow(id: id, title: title, in: app)
        XCTAssertTrue(
            destination.waitForExistence(timeout: 8)
                || !app.navigationBars["Playground"].exists,
            "Could not open experiment \(id)"
        )
    }

    private func tapLauncherRow(id: String, title: String, in app: XCUIApplication) {
        let byId = app.buttons["experiment-\(id)"]
        if byId.exists {
            byId.tap()
            return
        }
        app.staticTexts[title].tap()
    }

    /// Type `query` into the launcher search field when it is visible.
    @discardableResult
    private func filterLauncher(to query: String, in app: XCUIApplication) -> Bool {
        let search = app.searchFields["Search experiments"]
        if !search.exists {
            if app.navigationBars["Playground"].exists {
                app.navigationBars["Playground"].swipeDown()
            }
        }
        guard search.waitForExistence(timeout: 2) else { return false }
        search.tap()
        search.typeText(query)
        return true
    }

    /// Swipe the launcher list until `element` appears (or attempts are exhausted).
    @discardableResult
    private func scrollLauncherUntilExists(
        _ element: XCUIElement,
        in app: XCUIApplication,
        maxSwipes: Int = 10
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
        // Assert near-top rows before scrolling down — swipeUp-only helpers
        // cannot bring virtualized early rows back into view.
        XCTAssertTrue(app.staticTexts["Ride Monitor"].exists)
        XCTAssertTrue(app.staticTexts["Army List"].exists)
        XCTAssertTrue(app.staticTexts["T9 Keyboard"].exists)
        XCTAssertTrue(app.staticTexts["Follow the Hum"].exists)
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Local Lens"], in: app),
            "Local Lens should appear after scrolling the launcher"
        )
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Live Translate"], in: app),
            "Live Translate should appear after scrolling the launcher"
        )
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Voxel Eyes"], in: app),
            "Voxel Eyes should appear after scrolling the launcher"
        )
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["Wigglecam"], in: app),
            "Wigglecam should appear after scrolling the launcher"
        )
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["ESP32 BLE"], in: app),
            "ESP32 BLE should appear after scrolling the launcher"
        )
        XCTAssertTrue(
            scrollLauncherUntilExists(app.staticTexts["App Attest"], in: app),
            "App Attest should appear after scrolling the launcher"
        )
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

    func testVoxelWorldExperimentOpens() {
        let app = launchApp()

        openExperiment("voxel-world", title: "Voxel Eyes", in: app, navigationBarHidden: true)

        let backButton = app.buttons["voxelBackButton"]
        XCTAssertTrue(backButton.waitForExistence(timeout: 8))
        XCTAssertEqual(backButton.label, "Back")
        let captureButton = app.buttons["voxelCaptureButton"]
        XCTAssertTrue(captureButton.waitForExistence(timeout: 8)
            || app.otherElements["voxelCaptureButton"].waitForExistence(timeout: 3))
        let capture = captureButton.exists ? captureButton : app.otherElements["voxelCaptureButton"]
        XCTAssertEqual(capture.label, "Take picture")
        XCTAssertFalse(app.sliders["voxelSizeSlider"].exists)
        XCTAssertFalse(app.buttons["voxelResetButton"].exists)
        XCTAssertFalse(app.buttons["voxelFreezeCheckbox"].exists)
        XCTAssertFalse(app.buttons["voxelCameraFeedCheckbox"].exists)
        XCTAssertFalse(app.staticTexts["voxelStatusMessage"].exists)
        XCTAssertFalse(app.staticTexts["voxelCountLabel"].exists)
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

    func testLiveTranslateExperimentOpens() {
        let app = launchApp()

        openExperiment("live-translate", title: "Live Translate", in: app)

        XCTAssertTrue(app.navigationBars["Live Translate"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["liveTranslateLanguageButton"].waitForExistence(timeout: 8)
            || app.otherElements["liveTranslateLanguageButton"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.buttons["liveTranslateCopyButton"].waitForExistence(timeout: 8)
            || app.otherElements["liveTranslateCopyButton"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.buttons["liveTranslateFlipCameraButton"].waitForExistence(timeout: 8)
            || app.otherElements["liveTranslateFlipCameraButton"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["liveTranslateStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["liveTranslateStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["liveTranslateModelBadge"].waitForExistence(timeout: 3)
            || app.otherElements["liveTranslateModelBadge"].waitForExistence(timeout: 3)
            || app.staticTexts["liveTranslatePlaceholder"].waitForExistence(timeout: 3)
            || app.otherElements["liveTranslatePlaceholder"].waitForExistence(timeout: 3))
    }

    func testESP32BLEExperimentOpens() {
        let app = launchApp()

        openExperiment("esp32-ble", title: "ESP32 BLE", in: app)

        XCTAssertTrue(app.navigationBars["ESP32 BLE"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.buttons["esp32BleScanButton"].waitForExistence(timeout: 8)
            || app.otherElements["esp32BleScanButton"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["esp32BleStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["esp32BleStatusMessage"].waitForExistence(timeout: 3)
            || app.staticTexts["Flash esp32-ble, then scan."].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["esp32BleAvailabilityBanner"].waitForExistence(timeout: 8)
            || app.otherElements["esp32BleAvailabilityBanner"].waitForExistence(timeout: 3)
            || app.staticTexts["Bluetooth is on."].waitForExistence(timeout: 3)
            || app.staticTexts["BLE needs a physical iPhone. The Simulator cannot talk to an ESP32."].waitForExistence(timeout: 3))
        if !app.sliders["esp32BleBlinkSlider"].waitForExistence(timeout: 2) {
            app.swipeUp()
        }
        XCTAssertTrue(app.sliders["esp32BleBlinkSlider"].waitForExistence(timeout: 8)
            || app.otherElements["esp32BleBlinkSlider"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["esp32BleBlinkValue"].waitForExistence(timeout: 8)
            || app.otherElements["esp32BleBlinkValue"].waitForExistence(timeout: 3)
            || app.staticTexts["every 1s"].waitForExistence(timeout: 3))
    }

    func testAppAttestExperimentOpens() {
        let app = launchApp()

        openExperiment("app-attest", title: "App Attest", in: app)

        XCTAssertTrue(
            app.navigationBars["App Attest"].waitForExistence(timeout: 8)
                || app.otherElements["appAttestRoot"].waitForExistence(timeout: 4)
                || app.staticTexts["appAttestAvailabilityBanner"].waitForExistence(timeout: 4)
                || app.otherElements["appAttestAvailabilityBanner"].waitForExistence(timeout: 3)
        )
        XCTAssertTrue(app.buttons["appAttestSignInButton"].waitForExistence(timeout: 8)
            || app.otherElements["appAttestSignInButton"].waitForExistence(timeout: 3)
            || app.buttons["Sign in with Apple"].waitForExistence(timeout: 3)
            || app.staticTexts["appAttestAppleUserIdValue"].waitForExistence(timeout: 3)
            || app.otherElements["appAttestAppleUserIdValue"].waitForExistence(timeout: 3)
            || app.buttons["appAttestSignOutButton"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["appAttestStatusMessage"].waitForExistence(timeout: 8)
            || app.otherElements["appAttestStatusMessage"].waitForExistence(timeout: 3))
        XCTAssertTrue(app.staticTexts["appAttestAvailabilityBanner"].waitForExistence(timeout: 8)
            || app.otherElements["appAttestAvailabilityBanner"].waitForExistence(timeout: 3)
            || app.staticTexts["App Attest needs a physical iPhone. The Simulator cannot generate a hardware key."].waitForExistence(timeout: 3)
            || app.staticTexts["App Attest is available on this device."].waitForExistence(timeout: 3))
    }

    func testLayaExperimentOpens() {
        let app = launchApp()

        openExperiment("laya", title: "Laya", in: app)

        XCTAssertTrue(app.navigationBars["Laya"].waitForExistence(timeout: 8))
        XCTAssertTrue(app.staticTexts["layaStatus"].waitForExistence(timeout: 8)
            || app.otherElements["layaStatus"].waitForExistence(timeout: 3))
        // A fresh Simulator has no download, so the download button is the only action.
        XCTAssertTrue(app.buttons["layaDownloadButton"].waitForExistence(timeout: 8)
            || app.otherElements["layaDownloadButton"].waitForExistence(timeout: 3)
            || app.buttons["layaAskButton"].waitForExistence(timeout: 3))
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

        // Catalog loaded (empty library or list). Create must show the form —
        // never the dual-@State race message from older builds.
        let newButton = app.buttons["armyListNewButton"]
        XCTAssertTrue(newButton.waitForExistence(timeout: 8), "New list control missing")
        XCTAssertTrue(newButton.isEnabled, "New list should be enabled when the catalog loaded")
        newButton.tap()

        let nameField = app.descendants(matching: .any)["armyListNameField"]
        let sheetUnavailable = app.descendants(matching: .any)["armyListNewSheetUnavailable"]
        let raceMessage = app.staticTexts["The create sheet opened without a catalog snapshot."]
        let sheetReady = NSPredicate { _, _ in
            nameField.exists || sheetUnavailable.exists || raceMessage.exists
        }
        let sheetExpectation = XCTNSPredicateExpectation(predicate: sheetReady, object: app)
        XCTAssertEqual(
            XCTWaiter.wait(for: [sheetExpectation], timeout: 8),
            .completed,
            "New list sheet was blank — expected the create form"
        )

        XCTAssertFalse(
            raceMessage.exists,
            "Catalog must ride on the sheet(item:) payload; dual @State raced on device"
        )
        XCTAssertFalse(
            sheetUnavailable.exists,
            "Catalog is loaded, so New list must not show Cannot create a list"
        )
        XCTAssertTrue(
            nameField.waitForExistence(timeout: 3),
            "Expected the create form (name field) when the catalog is bundled"
        )

        let starter = app.buttons["armyListBuildStarterButton"]
        XCTAssertTrue(
            starter.waitForExistence(timeout: 3),
            "Expected Build starter list on the create sheet"
        )
        XCTAssertTrue(starter.isEnabled)

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
        let editorCover = app.descendants(matching: .any)["armyListEditorCover"]
        let editorUnavailable = app.descendants(matching: .any)["armyListEditorUnavailable"]
        let editorReady = NSPredicate { _, _ in
            legalBadge.exists || validationBanner.exists || editorCover.exists || editorUnavailable.exists
        }
        let editorExpectation = XCTNSPredicateExpectation(predicate: editorReady, object: app)
        XCTAssertEqual(
            XCTWaiter.wait(for: [editorExpectation], timeout: 10),
            .completed,
            "Create did not open the editor"
        )

        XCTAssertFalse(
            editorUnavailable.exists,
            "Editor must open with the catalog from the create payload"
        )
        XCTAssertTrue(
            legalBadge.waitForExistence(timeout: 5) || validationBanner.exists,
            "Editor should show live validation for the new empty list"
        )

        // Name, battle size, and detachments now live on the Army settings page,
        // so the editor stays focused on units. Open settings to rename.
        let settingsLink = app.descendants(matching: .any)["armyListSettingsLink"]
        XCTAssertTrue(
            settingsLink.waitForExistence(timeout: 3),
            "Editor must offer an Army settings page"
        )
        settingsLink.tap()

        let settingsName = app.descendants(matching: .any)["armyListSettingsNameField"]
        XCTAssertTrue(
            settingsName.waitForExistence(timeout: 3),
            "Army settings must let you rename the list"
        )
        if let value = settingsName.value as? String {
            XCTAssertEqual(value, listName, "Settings name field should show the name from create")
        }
        XCTAssertTrue(
            app.descendants(matching: .any)["armyListSettingsBattleSizePicker"].waitForExistence(timeout: 3),
            "Army settings must let you change battle size"
        )

        // Back to the editor.
        app.navigationBars.buttons.element(boundBy: 0).tap()

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
