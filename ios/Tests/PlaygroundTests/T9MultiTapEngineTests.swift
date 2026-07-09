import XCTest
@testable import Playground

final class T9MultiTapEngineTests: XCTestCase {
    private var inserted: [String] = []
    private var deletions = 0
    private var engine: T9MultiTapEngine!

    override func setUp() {
        super.setUp()
        inserted = []
        deletions = 0
        // Use a serial queue we control so tests don't race the real main run loop.
        let queue = DispatchQueue(label: "t9.test")
        engine = T9MultiTapEngine(
            queue: queue,
            onInsert: { [weak self] text in self?.inserted.append(text) },
            onDeleteBackward: { [weak self] in self?.deletions += 1 }
        )
        engine.commitDelay = 10 // long enough that auto-commit never fires mid-test
    }

    private var text: String { inserted.joined() }

    func testKey2CyclesABCThenDigit() {
        engine.tap(.digit(2))
        XCTAssertEqual(engine.pendingPreview.lowercased(), "a")
        engine.tap(.digit(2))
        XCTAssertEqual(engine.pendingPreview.lowercased(), "b")
        engine.tap(.digit(2))
        XCTAssertEqual(engine.pendingPreview.lowercased(), "c")
        engine.tap(.digit(2))
        XCTAssertEqual(engine.pendingPreview, "2")
        engine.tap(.digit(2))
        XCTAssertEqual(engine.pendingPreview.lowercased(), "a")
    }

    func testDifferentKeyCommitsPrevious() {
        engine.tap(.digit(2)) // pending a
        engine.tap(.digit(3)) // commit a, pending d
        XCTAssertEqual(text.lowercased(), "a")
        XCTAssertEqual(engine.pendingPreview.lowercased(), "d")
        engine.commitPending()
        XCTAssertEqual(text.lowercased(), "ad")
    }

    func testHashInsertsSpace() {
        engine.tap(.digit(2))
        engine.tap(.hash)
        XCTAssertEqual(text.lowercased(), "a ")
        XCTAssertNil(engine.pendingCharacter)
    }

    func testStarCyclesShiftModes() {
        XCTAssertEqual(engine.shiftMode, .lowercase)
        engine.tap(.star)
        XCTAssertEqual(engine.shiftMode, .uppercaseOnce)
        engine.tap(.star)
        XCTAssertEqual(engine.shiftMode, .capsLock)
        engine.tap(.star)
        XCTAssertEqual(engine.shiftMode, .numbers)
        engine.tap(.star)
        XCTAssertEqual(engine.shiftMode, .lowercase)
    }

    func testUppercaseOnceThenReturnsToLowercase() {
        engine.tap(.star) // Abc
        engine.tap(.digit(2))
        engine.commitPending()
        XCTAssertEqual(text, "A")
        XCTAssertEqual(engine.shiftMode, .lowercase)

        engine.tap(.digit(2))
        engine.commitPending()
        XCTAssertEqual(text, "Aa")
    }

    func testCapsLockStaysUppercase() {
        engine.tap(.star)
        engine.tap(.star) // ABC
        engine.tap(.digit(2))
        engine.commitPending()
        engine.tap(.digit(3))
        engine.commitPending()
        XCTAssertEqual(text, "AD")
        XCTAssertEqual(engine.shiftMode, .capsLock)
    }

    func testNumbersModeInsertsDigitsImmediately() {
        engine.tap(.star)
        engine.tap(.star)
        engine.tap(.star) // 123
        engine.tap(.digit(5))
        engine.tap(.digit(5))
        XCTAssertEqual(text, "55")
        XCTAssertNil(engine.pendingCharacter)
    }

    func testLongPressInsertsDigit() {
        engine.longPress(.digit(7))
        XCTAssertEqual(text, "7")
    }

    func testDeleteCancelsPendingThenDeletes() {
        engine.tap(.digit(2))
        engine.deleteBackward()
        XCTAssertEqual(text, "")
        XCTAssertNil(engine.pendingCharacter)
        XCTAssertEqual(deletions, 0)

        engine.tap(.digit(2))
        engine.commitPending()
        engine.deleteBackward()
        XCTAssertEqual(deletions, 1)
    }

    func testKey7HasFourLetters() {
        XCTAssertEqual(T9PadKey.digit(7).letters.map(String.init).joined(), "pqrs7")
        engine.tap(.digit(7))
        engine.tap(.digit(7))
        engine.tap(.digit(7))
        engine.tap(.digit(7))
        XCTAssertEqual(engine.pendingPreview.lowercased(), "s")
        engine.tap(.digit(7))
        XCTAssertEqual(engine.pendingPreview, "7")
    }

    func testZeroCyclesSpaceAndZero() {
        engine.tap(.digit(0))
        XCTAssertEqual(engine.pendingPreview, " ")
        engine.tap(.digit(0))
        XCTAssertEqual(engine.pendingPreview, "0")
    }
}
