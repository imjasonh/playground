import XCTest
@testable import Roll

final class StatusClickTests: XCTestCase {
    func testLeftClickRolls() {
        XCTAssertEqual(StatusClick(rightMouse: false, control: false), .roll)
    }

    func testRightClickOpensMenu() {
        XCTAssertEqual(StatusClick(rightMouse: true, control: false), .menu)
    }

    func testControlClickOpensMenu() {
        XCTAssertEqual(StatusClick(rightMouse: false, control: true), .menu)
    }
}
