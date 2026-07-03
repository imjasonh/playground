import XCTest
@testable import HelloIOS

final class TemperatureConverterTests: XCTestCase {
    private let accuracy = 0.0001

    func testCelsiusToFahrenheitKnownValues() {
        XCTAssertEqual(TemperatureConverter.celsiusToFahrenheit(0), 32, accuracy: accuracy)
        XCTAssertEqual(TemperatureConverter.celsiusToFahrenheit(100), 212, accuracy: accuracy)
        XCTAssertEqual(TemperatureConverter.celsiusToFahrenheit(37), 98.6, accuracy: accuracy)
    }

    func testFahrenheitToCelsiusKnownValues() {
        XCTAssertEqual(TemperatureConverter.fahrenheitToCelsius(32), 0, accuracy: accuracy)
        XCTAssertEqual(TemperatureConverter.fahrenheitToCelsius(212), 100, accuracy: accuracy)
        XCTAssertEqual(TemperatureConverter.fahrenheitToCelsius(98.6), 37, accuracy: accuracy)
    }

    /// -40 is the fixed point where both scales meet.
    func testMinusFortyIsTheFixedPoint() {
        XCTAssertEqual(TemperatureConverter.celsiusToFahrenheit(-40), -40, accuracy: accuracy)
        XCTAssertEqual(TemperatureConverter.fahrenheitToCelsius(-40), -40, accuracy: accuracy)
    }

    /// Converting there and back should return the original value.
    func testRoundTripIsStable() {
        for value in stride(from: -100.0, through: 100.0, by: 12.5) {
            let roundTrip = TemperatureConverter.fahrenheitToCelsius(
                TemperatureConverter.celsiusToFahrenheit(value)
            )
            XCTAssertEqual(roundTrip, value, accuracy: accuracy)
        }
    }

    func testConvertRespectsSourceScale() {
        XCTAssertEqual(TemperatureConverter.convert(0, from: .celsius), 32, accuracy: accuracy)
        XCTAssertEqual(TemperatureConverter.convert(32, from: .fahrenheit), 0, accuracy: accuracy)
    }

    func testScaleOppositeAndUnit() {
        XCTAssertEqual(TemperatureScale.celsius.opposite, .fahrenheit)
        XCTAssertEqual(TemperatureScale.fahrenheit.opposite, .celsius)
        XCTAssertEqual(TemperatureScale.celsius.unit, "°C")
        XCTAssertEqual(TemperatureScale.fahrenheit.unit, "°F")
    }
}
