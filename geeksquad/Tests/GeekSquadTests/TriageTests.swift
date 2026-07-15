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

    func testInstructionsStayInNetworkScope() {
        let text = TriageInstructions.text
        XCTAssertTrue(text.localizedCaseInsensitiveContains("network"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("do not call diagnostic tools"))
    }
}

final class TriageFailureMessageTests: XCTestCase {
    func testOpaqueGenerationErrorCopyIsActionable() {
        let error = NSError(
            domain: "FoundationModels.LanguageModelSession.GenerationError",
            code: -1,
            userInfo: [
                NSLocalizedDescriptionKey:
                    "The operation couldn’t be completed. (FoundationModels.LanguageModelSession.GenerationError error -1.)",
            ]
        )
        let message = TriageFailureMessage.from(error)
        XCTAssertFalse(message.contains("error -1"))
        XCTAssertFalse(message.localizedCaseInsensitiveContains("Triage failed"))
        XCTAssertTrue(message.localizedCaseInsensitiveContains("New chat"))
        XCTAssertTrue(message.localizedCaseInsensitiveContains("Toolbox"))
    }

    func testGenericNSErrorStillPointsAtRecovery() {
        let error = NSError(domain: "Test", code: 42, userInfo: [
            NSLocalizedDescriptionKey: "disk full",
        ])
        let message = TriageFailureMessage.from(error)
        XCTAssertTrue(message.localizedCaseInsensitiveContains("New chat"))
        XCTAssertTrue(message.contains("disk full"))
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
