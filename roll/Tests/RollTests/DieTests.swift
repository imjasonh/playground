import XCTest
@testable import Roll

final class DieTests: XCTestCase {
    func testStartsUnrolled() {
        let die = Die()
        XCTAssertNil(die.face)
        XCTAssertEqual(die.symbolName, "dice")
        XCTAssertEqual(die.statusText, "Not rolled yet")
    }

    func testRollUsesSuppliedFace() {
        var die = Die()
        XCTAssertEqual(die.roll { .four }, .four)
        XCTAssertEqual(die.face, .four)
        XCTAssertEqual(die.symbolName, "die.face.4")
        XCTAssertEqual(die.statusText, "Showing 4")
    }

    func testSecondRollReplacesTheFace() {
        var die = Die()
        die.roll { .two }
        die.roll { .six }
        XCTAssertEqual(die.face, .six)
        XCTAssertEqual(die.symbolName, "die.face.6")
    }

    func testSymbolNamesMatchSFSymbols() {
        let names = DieFace.allCases.map(\.symbolName)
        XCTAssertEqual(
            names,
            [
                "die.face.1",
                "die.face.2",
                "die.face.3",
                "die.face.4",
                "die.face.5",
                "die.face.6",
            ]
        )
    }

    func testFairFaceIsOneOfTheSix() {
        for _ in 0..<40 {
            XCTAssertTrue(DieFace.allCases.contains(Die.fairFace()))
        }
    }
}
