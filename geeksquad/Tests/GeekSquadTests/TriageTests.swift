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

final class AppleIntelligenceSettingsTests: XCTestCase {
    func testPreferenceURLsPointAtSystemSettings() {
        XCTAssertFalse(AppleIntelligenceSettings.preferenceURLs.isEmpty)
        for url in AppleIntelligenceSettings.preferenceURLs {
            XCTAssertEqual(url.scheme, "x-apple.systempreferences")
        }
        XCTAssertEqual(
            AppleIntelligenceSettings.preferenceURLs.first?.absoluteString,
            "x-apple.systempreferences:com.apple.Siri-Settings.extension"
        )
    }
}
