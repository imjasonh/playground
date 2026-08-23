import XCTest
@testable import Playground

final class DeviceAgentTests: XCTestCase {
    func testFallbackPlannerMapsContactsAndLocation() {
        let plan = AgentFallbackPlanner.steps(for: "Find contact Mom and where am I", mode: .act)
        let names = plan.steps.map(\.tool)
        XCTAssertTrue(names.contains("searchContacts"))
        XCTAssertTrue(names.contains("getCurrentLocation"))
    }

    func testFallbackPlannerMapsAttachments() {
        let plan = AgentFallbackPlanner.steps(for: "list attachments in the inbox", mode: .observe)
        XCTAssertEqual(plan.steps.first?.tool, "listAttachments")
    }

    func testFallbackPlannerHelp() {
        let plan = AgentFallbackPlanner.steps(for: "help", mode: .browse)
        XCTAssertTrue(plan.steps.isEmpty)
        XCTAssertTrue(plan.coda.localizedCaseInsensitiveContains("tool"))
    }

    func testFallbackPlannerDemoBrowser() {
        let plan = AgentFallbackPlanner.steps(for: "open demo mail browser", mode: .browse)
        XCTAssertTrue(plan.steps.map(\.tool).contains("browserLoadDemo"))
    }

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

    func testOpenURLIgnoresOtherSchemes() {
        let url = URL(string: "https://example.com")!
        XCTAssertFalse(AgentInbox.shared.handleOpenURL(url))
    }

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

        let listed = AgentToolExecutor.listAttachments(context: AgentToolContext(inbox: inbox))
        XCTAssertTrue(listed.contains("note.txt"))
    }

    func testPermissionDomainPrePromptIsNonEmpty() {
        for domain in AgentPermissionDomain.allCases {
            XCTAssertFalse(domain.prePrompt.isEmpty)
            XCTAssertFalse(domain.title.isEmpty)
        }
    }
}
