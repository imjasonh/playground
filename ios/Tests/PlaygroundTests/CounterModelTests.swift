import XCTest
@testable import Playground

final class CounterModelTests: XCTestCase {
    func testStartsAtInitialValueClampedIntoRange() {
        XCTAssertEqual(CounterModel(value: 5, minimum: 0, maximum: 10).value, 5)
        XCTAssertEqual(CounterModel(value: -3, minimum: 0, maximum: 10).value, 0)
        XCTAssertEqual(CounterModel(value: 42, minimum: 0, maximum: 10).value, 10)
    }

    func testIncrementStopsAtMaximum() {
        var model = CounterModel(value: 9, minimum: 0, maximum: 10)
        model.increment()
        XCTAssertEqual(model.value, 10)
        XCTAssertFalse(model.canIncrement)
        model.increment() // no-op at the ceiling
        XCTAssertEqual(model.value, 10)
    }

    func testDecrementStopsAtMinimum() {
        var model = CounterModel(value: 1, minimum: 0, maximum: 10)
        model.decrement()
        XCTAssertEqual(model.value, 0)
        XCTAssertFalse(model.canDecrement)
        model.decrement() // no-op at the floor
        XCTAssertEqual(model.value, 0)
    }

    func testResetReturnsToZeroWithinRange() {
        var model = CounterModel(value: 7, minimum: 0, maximum: 10)
        model.reset()
        XCTAssertEqual(model.value, 0)

        // When 0 is outside the range, reset clamps into it.
        var shifted = CounterModel(value: 5, minimum: 3, maximum: 8)
        shifted.reset()
        XCTAssertEqual(shifted.value, 3)
    }

    func testIncrementDecrementFlags() {
        let mid = CounterModel(value: 5, minimum: 0, maximum: 10)
        XCTAssertTrue(mid.canIncrement)
        XCTAssertTrue(mid.canDecrement)
    }
}
