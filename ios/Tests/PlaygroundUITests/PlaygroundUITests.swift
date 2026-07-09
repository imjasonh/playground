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
        XCTAssertTrue(app.staticTexts["Temperature Converter"].exists)
        XCTAssertTrue(app.staticTexts["Counter"].exists)
    }

    func testTemperatureConverterExperiment() {
        let app = XCUIApplication()
        app.launch()

        openExperiment("temperature-converter", title: "Temperature Converter", in: app)

        let input = app.textFields["temperatureInput"]
        XCTAssertTrue(input.waitForExistence(timeout: 5))
        input.tap()
        input.typeText("100")

        let result = app.staticTexts["convertedResult"]
        XCTAssertTrue(result.waitForExistence(timeout: 5))
        XCTAssertTrue(result.label.contains("212.0"))
        XCTAssertTrue(result.label.contains("°F"))
    }

    func testCounterExperiment() {
        let app = XCUIApplication()
        app.launch()

        openExperiment("counter", title: "Counter", in: app)

        let value = app.staticTexts["counterValue"]
        XCTAssertTrue(value.waitForExistence(timeout: 5))
        XCTAssertEqual(value.label, "0")

        app.buttons["incrementButton"].tap()
        app.buttons["incrementButton"].tap()
        XCTAssertEqual(value.label, "2")

        app.buttons["decrementButton"].tap()
        XCTAssertEqual(value.label, "1")

        app.buttons["resetButton"].tap()
        XCTAssertEqual(value.label, "0")
    }
}
