import XCTest
@testable import HelloMac

final class GreetingTests: XCTestCase {
    func testDefaultGreeting() {
        XCTAssertEqual(Greeting().text, "Hello, Mac!")
    }

    func testCustomName() {
        XCTAssertEqual(Greeting(name: "Playground").text, "Hello, Playground!")
    }

    func testBlankNameFallsBackToMac() {
        XCTAssertEqual(Greeting(name: "   ").text, "Hello, Mac!")
        XCTAssertEqual(Greeting(name: "").text, "Hello, Mac!")
    }
}
