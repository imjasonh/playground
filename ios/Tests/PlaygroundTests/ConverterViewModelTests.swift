import XCTest
@testable import Playground

@MainActor
final class ConverterViewModelTests: XCTestCase {
    func testEmptyInputShowsPlaceholder() {
        let vm = ConverterViewModel()
        vm.inputText = ""
        XCTAssertNil(vm.parsedValue)
        XCTAssertEqual(vm.convertedText, ConverterViewModel.placeholder)
    }

    func testNonNumericInputShowsPlaceholder() {
        let vm = ConverterViewModel()
        vm.inputText = "boiling"
        XCTAssertNil(vm.parsedValue)
        XCTAssertEqual(vm.convertedText, ConverterViewModel.placeholder)
    }

    func testWhitespaceIsTrimmed() {
        let vm = ConverterViewModel()
        vm.inputText = "  100  "
        XCTAssertEqual(vm.parsedValue, 100)
        XCTAssertEqual(vm.convertedText, "212.0")
    }

    func testCelsiusConversion() {
        let vm = ConverterViewModel()
        vm.scale = .celsius
        vm.inputText = "100"
        XCTAssertEqual(vm.convertedText, "212.0")
        XCTAssertEqual(vm.inputUnit, "°C")
        XCTAssertEqual(vm.resultUnit, "°F")
    }

    func testToggleScaleFlipsConversionAndUnits() {
        let vm = ConverterViewModel()
        vm.inputText = "100"
        XCTAssertEqual(vm.convertedText, "212.0")

        vm.toggleScale()

        XCTAssertEqual(vm.scale, .fahrenheit)
        XCTAssertEqual(vm.inputUnit, "°F")
        XCTAssertEqual(vm.resultUnit, "°C")
        XCTAssertEqual(vm.convertedText, "37.8") // 100°F ≈ 37.8°C
    }

    func testInfiniteInputIsRejected() {
        let vm = ConverterViewModel()
        vm.inputText = "inf"
        XCTAssertNil(vm.parsedValue)
        XCTAssertEqual(vm.convertedText, ConverterViewModel.placeholder)
    }

    func testFormatRoundsToOneDecimalAndNormalizesNegativeZero() {
        XCTAssertEqual(ConverterViewModel.format(37.849), "37.8")
        XCTAssertEqual(ConverterViewModel.format(37.851), "37.9")
        XCTAssertEqual(ConverterViewModel.format(-0.0001), "0.0")
    }
}
