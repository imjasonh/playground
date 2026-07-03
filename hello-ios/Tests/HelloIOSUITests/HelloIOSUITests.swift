import XCTest

/// Smoke-level UI tests that drive the real app through the accessibility
/// identifiers declared in `ContentView`.
final class HelloIOSUITests: XCTestCase {
    override func setUp() {
        super.setUp()
        continueAfterFailure = false
    }

    func testConvertsCelsiusInputToFahrenheit() {
        let app = XCUIApplication()
        app.launch()

        let input = app.textFields["temperatureInput"]
        XCTAssertTrue(input.waitForExistence(timeout: 5))
        input.tap()
        input.typeText("100")

        let result = app.staticTexts["convertedResult"]
        XCTAssertTrue(result.waitForExistence(timeout: 5))
        XCTAssertTrue(result.label.contains("212.0"))
        XCTAssertTrue(result.label.contains("°F"))
    }

    func testSwapButtonChangesResultUnit() {
        let app = XCUIApplication()
        app.launch()

        let input = app.textFields["temperatureInput"]
        XCTAssertTrue(input.waitForExistence(timeout: 5))
        input.tap()
        input.typeText("100")

        app.buttons["swapButton"].tap()

        let result = app.staticTexts["convertedResult"]
        XCTAssertTrue(result.waitForExistence(timeout: 5))
        XCTAssertTrue(result.label.contains("°C"))
    }
}
