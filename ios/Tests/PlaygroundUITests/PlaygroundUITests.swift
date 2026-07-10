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
        XCTAssertTrue(app.staticTexts["Follow the Hum"].exists)
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

        // Smoke-test that the experiment pushed; multi-tap logic is covered by
        // T9MultiTapEngineTests unit tests.
        XCTAssertTrue(app.navigationBars["T9 Keyboard"].waitForExistence(timeout: 5))
        XCTAssertTrue(app.buttons["t9DemoDeleteButton"].waitForExistence(timeout: 5))
        XCTAssertTrue(app.buttons["t9DemoClearButton"].waitForExistence(timeout: 5))
    }

    func testFollowTheHumExperimentOpens() {
        let app = XCUIApplication()
        app.launch()

        openExperiment("follow-the-hum", title: "Follow the Hum", in: app)

        XCTAssertTrue(app.navigationBars["Follow the Hum"].waitForExistence(timeout: 5))
        XCTAssertTrue(app.buttons["startHumHuntButton"].waitForExistence(timeout: 5))
        XCTAssertTrue(app.otherElements["humStatusMessage"].waitForExistence(timeout: 5)
            || app.staticTexts["humStatusMessage"].waitForExistence(timeout: 2)
            || app.staticTexts["Put on AirPods, then start a hunt."].waitForExistence(timeout: 2))
    }
}
