import XCTest
@testable import Playground

final class DeviceAgentTests: XCTestCase {
    @MainActor
    func testRuntimeReportsUnavailableWithoutFoundationModels() {
        let runtime = AgentRuntime()
        runtime.refreshModelStatus()
        // Simulator / CI and pre–iOS 26 devices have no Apple Intelligence model.
        XCTAssertFalse(runtime.isModelAvailable)
        XCTAssertNotEqual(runtime.modelGate, .available)
        switch runtime.modelGate {
        case .unsupportedPlatform, .deviceNotEligible, .needsAppleIntelligence, .modelNotReady, .other:
            break
        case .available:
            XCTFail("Expected unavailable gate on this build")
        }
        XCTAssertFalse(runtime.modelGate.title.isEmpty)
        XCTAssertFalse(runtime.modelGate.detail.isEmpty)
    }

    @MainActor
    func testModelGateActionsForInstallStates() {
        XCTAssertEqual(AgentModelGate.needsAppleIntelligence.primaryAction, .openAppleIntelligenceSettings)
        XCTAssertEqual(AgentModelGate.modelNotReady.primaryAction, .checkAgain)
        XCTAssertNil(AgentModelGate.deviceNotEligible.primaryAction)
        XCTAssertNil(AgentModelGate.unsupportedPlatform.primaryAction)
        XCTAssertEqual(
            AgentModelGateAction.openAppleIntelligenceSettings.title,
            "Open Apple Intelligence Settings"
        )
        XCTAssertEqual(AgentModelGateAction.checkAgain.title, "Check again")
    }

    @MainActor
    func testSendWhileUnavailableDoesNotRunTools() async throws {
        let runtime = AgentRuntime()
        runtime.refreshModelStatus()
        XCTAssertFalse(runtime.isModelAvailable)
        let before = runtime.transcript.count
        await runtime.send(prompt: "list attachments", source: .chat)
        XCTAssertGreaterThan(runtime.transcript.count, before)
        let last = try XCTUnwrap(runtime.transcript.last)
        XCTAssertEqual(last.kind, .system)
        XCTAssertFalse(runtime.transcript.contains { entry in
            if case .toolCall = entry.kind { return true }
            return false
        })
    }

    @MainActor
    func testDeepLinkParsesPrompt() {
        let url = URL(string: "playground://device-agent?prompt=hello%20world&voice=1&mode=browse")!
        let inbox = AgentInbox.shared
        XCTAssertTrue(inbox.handleOpenURL(url))
        let run = inbox.consumePendingRun()
        XCTAssertEqual(run?.prompt, "hello world")
        XCTAssertEqual(run?.mode, .browse)
        XCTAssertEqual(run?.preferVoice, true)
        XCTAssertEqual(run?.source, .deepLink)
    }

    @MainActor
    func testOpenURLIgnoresOtherSchemes() {
        let url = URL(string: "https://example.com")!
        XCTAssertFalse(AgentInbox.shared.handleOpenURL(url))
    }

    @MainActor
    func testSanitizeAndImportRoundTrip() throws {
        let inbox = AgentInbox.shared
        let temp = FileManager.default.temporaryDirectory
            .appendingPathComponent("device-agent-test-\(UUID().uuidString).txt")
        try "hello agent".write(to: temp, atomically: true, encoding: .utf8)
        defer { try? FileManager.default.removeItem(at: temp) }

        let attachment = try inbox.importFile(from: temp, preferredName: "note.txt")
        XCTAssertEqual(attachment.filename, "note.txt")
        XCTAssertGreaterThan(attachment.byteCount, 0)
        let url = try XCTUnwrap(inbox.fileURL(for: attachment))
        let text = try String(contentsOf: url, encoding: .utf8)
        XCTAssertEqual(text, "hello agent")

        let listed = AgentToolExecutor.listAttachments(
            context: AgentToolContext(inbox: inbox)
        )
        XCTAssertTrue(listed.contains("note.txt"))
    }

    func testPermissionDomainPrePromptIsNonEmpty() {
        for domain in AgentPermissionDomain.allCases {
            XCTAssertFalse(domain.prePrompt.isEmpty)
            XCTAssertFalse(domain.title.isEmpty)
        }
    }
}
