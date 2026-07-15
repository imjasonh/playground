import XCTest
@testable import GeekSquad

final class TriageInstructionsTests: XCTestCase {
    func testInstructionsCoverProposeOnly() {
        let text = TriageInstructions.text
        XCTAssertTrue(text.localizedCaseInsensitiveContains("Geek Squad"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("tool"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("propose"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("Never"))
    }
}

final class ChatMessageTests: XCTestCase {
    func testIdentifiable() {
        let a = ChatMessage(role: .user, text: "hi")
        let b = ChatMessage(role: .assistant, text: "hello")
        XCTAssertNotEqual(a.id, b.id)
    }
}
