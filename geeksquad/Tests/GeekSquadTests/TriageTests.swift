import XCTest
@testable import GeekSquad

final class TriageInstructionsTests: XCTestCase {
    func testInstructionsCoverProposeOnly() {
        let text = TriageInstructions.text
        XCTAssertTrue(text.localizedCaseInsensitiveContains("Geek Squad"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("tool"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("proposedSteps"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("read-only"))
    }

    func testInstructionsIncludeProcessDiagnostics() {
        let text = TriageInstructions.text
        XCTAssertTrue(text.localizedCaseInsensitiveContains("process_usage"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("memory"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("disk_space"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("listening_ports"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("ping"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("traceroute"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("dns_trace"))
        XCTAssertTrue(text.localizedCaseInsensitiveContains("arp_neighbors"))
    }

    func testAudienceLimitsHardwareUpgrades() {
        XCTAssertTrue(TriageAudience.guidance.localizedCaseInsensitiveContains("RAM"))
        XCTAssertTrue(TriageAudience.guidance.localizedCaseInsensitiveContains("Do NOT recommend"))
        XCTAssertTrue(TriageAudience.guidance.localizedCaseInsensitiveContains("resolv.conf"))
        XCTAssertTrue(TriageAudience.guidance.localizedCaseInsensitiveContains("You run the diagnostics"))
        XCTAssertTrue(TriageInstructions.text.contains(TriageAudience.guidance))
        XCTAssertTrue(TriageGate.instructions.contains(TriageAudience.guidance))
        XCTAssertTrue(TriageInstructions.text.localizedCaseInsensitiveContains("Never tell the user to inspect"))
    }
}

final class TriageGateTests: XCTestCase {
    func testDiagnoseSentinelRoutesToTools() {
        XCTAssertNil(TriageGate.directAnswer(from: "DIAGNOSE"))
        XCTAssertNil(TriageGate.directAnswer(from: "diagnose\n"))
        XCTAssertNil(TriageGate.directAnswer(from: "DIAGNOSE because Wi-Fi looks broken"))
        XCTAssertTrue(TriageGate.needsDiagnostics("DIAGNOSE"))
    }

    func testSimpleAskReturnsDirectAnswer() {
        let answer = TriageGate.directAnswer(
            from: "That sounds like app performance, not the network. Open Activity Monitor and check CPU for Cursor."
        )
        XCTAssertEqual(
            answer,
            "That sounds like app performance, not the network. Open Activity Monitor and check CPU for Cursor."
        )
    }
}

final class TriageHeuristicsTests: XCTestCase {
    func testMemoryAndSlowAppNeedLiveDiagnostics() {
        XCTAssertTrue(TriageHeuristics.needsLiveDiagnostics("Tell me whether it's using too much memory"))
        XCTAssertTrue(TriageHeuristics.needsLiveDiagnostics("Cursor app is slow"))
        XCTAssertTrue(TriageHeuristics.needsLiveDiagnostics("DNS feels wrong on this Mac"))
        XCTAssertFalse(TriageHeuristics.needsLiveDiagnostics("What does Geek Squad do?"))
    }

    func testRecheckChipNeedsLiveDiagnostics() {
        let recheck =
            "Please re-run the most relevant live checks for my last question and tell me what changed."
        XCTAssertTrue(TriageHeuristics.isRecheckFollowUp(recheck))
        XCTAssertTrue(TriageHeuristics.needsLiveDiagnostics(recheck))
        XCTAssertTrue(TriageHeuristics.isRecheckFollowUp("Can you check again?"))
        XCTAssertTrue(TriageHeuristics.needsLiveDiagnostics("Run the same checks and say what changed."))
    }

    func testFocusRouting() {
        XCTAssertEqual(TriageHeuristics.focus(for: "Cursor is using too much memory"), .performance)
        XCTAssertEqual(TriageHeuristics.focus(for: "disk almost full"), .performance)
        XCTAssertEqual(TriageHeuristics.focus(for: "port 3000 already in use"), .functionality)
        XCTAssertEqual(TriageHeuristics.focus(for: "Safari crashed"), .functionality)
        XCTAssertEqual(TriageHeuristics.focus(for: "VPN DNS broken"), .network)
        XCTAssertEqual(TriageHeuristics.focus(for: "Please traceroute example.com for packet loss"), .network)
        XCTAssertEqual(TriageHeuristics.focus(for: "Ping 1.1.1.1 and check latency"), .network)
        // Recheck text alone has no focus keywords — chat model reuses prior turn.
        XCTAssertNil(TriageHeuristics.focus(for: "Please re-run the most relevant live checks for my last question and tell me what changed."))
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
