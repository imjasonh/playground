import XCTest

/// Smoke-level UI tests that drive the launcher and its experiments through the
/// accessibility identifiers declared in the views.
final class PlaygroundUITests: XCTestCase {
    override func setUp() {
        super.setUp()
        continueAfterFailure = false
    }

    /// Tap an experiment's launcher row, tolerating whether SwiftUI exposes the
    /// row as a button/cell (by identifier) or only its title text.
    private func openExperiment(_ id: String, title: String, in app: XCUIApplication) {
        let byId = app.buttons["experiment-\(id)"]
        if byId.waitForExistence(timeout: 5) {
            byId.tap()
            return
        }
        let byTitle = app.staticTexts[title]
        XCTAssertTrue(byTitle.waitForExistence(timeout: 5), "Could not find launcher row for \(id)")
        byTitle.tap()
    }

    func testLauncherListsExperiments() {
        let app = XCUIApplication()
        app.launch()

        XCTAssertTrue(app.navigationBars["Playground"].waitForExistence(timeout: 5))
        XCTAssertTrue(app.staticTexts["Ride Monitor"].exists)
        XCTAssertTrue(app.staticTexts["T9 Keyboard"].exists)
    }

    func testRideMonitorExperimentOpens() {
        let app = XCUIApplication()
        app.launch()

        openExperiment("ride-monitor", title: "Ride Monitor", in: app)

        XCTAssertTrue(app.buttons["startRideButton"].waitForExistence(timeout: 5))
    }

    func testT9KeyboardExperimentOpens() {
        let app = XCUIApplication()
        app.launch()

        openExperiment("t9-keyboard", title: "T9 Keyboard", in: app)

        XCTAssertTrue(app.buttons["t9OpenSettingsButton"].waitForExistence(timeout: 5))
        XCTAssertTrue(app.buttons["t9-key-2"].waitForExistence(timeout: 5))
    }
}
