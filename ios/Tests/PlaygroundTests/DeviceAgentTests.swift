import XCTest
@testable import Playground

final class DeviceAgentTests: XCTestCase {
    @MainActor
    func testRuntimeReportsModelGate() {
        let runtime = AgentRuntime()
        runtime.refreshModelStatus()
        // CI’s iOS 26 Simulator may report `.available`; older / ineligible
        // hosts report an unavailable gate. Either way the copy must be set.
        XCTAssertFalse(runtime.modelGate.title.isEmpty)
        XCTAssertFalse(runtime.modelGate.detail.isEmpty)
        XCTAssertEqual(runtime.isModelAvailable, runtime.modelGate.isAvailable)
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
    func testSendDoesNotCrashAndRecordsTranscript() async throws {
        let runtime = AgentRuntime()
        runtime.refreshModelStatus()
        let before = runtime.transcript.count
        await runtime.send(prompt: "list attachments", source: .chat)
        XCTAssertGreaterThan(runtime.transcript.count, before)

        if !runtime.isModelAvailable {
            let last = try XCTUnwrap(runtime.transcript.last)
            XCTAssertEqual(last.kind, .system)
            XCTAssertFalse(runtime.transcript.contains { entry in
                if case .toolCall = entry.kind { return true }
                return false
            })
        }
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

    @MainActor
    func testWatchDueAndAutomationNudgeHeuristics() throws {
        let suiteName = "device-agent-watch-tests-\(UUID().uuidString)"
        let suite = try XCTUnwrap(UserDefaults(suiteName: suiteName))
        defer { suite.removePersistentDomain(forName: suiteName) }
        let store = AgentWatchStore(userDefaults: suite)

        XCTAssertFalse(store.needsAutomationNudge)
        store.addWatch(title: "PR", prompt: "Any new review comments?", intervalHours: 24)
        XCTAssertTrue(store.needsAutomationNudge)
        XCTAssertEqual(store.dueWatches().count, 1)

        store.userMarkedAutomationConfigured = true
        XCTAssertTrue(store.isAutomaticCheckStale)
        XCTAssertTrue(store.needsAutomationNudge)

        let due = store.recordAutomaticCheck()
        XCTAssertEqual(due.count, 1)
        XCTAssertFalse(store.isAutomaticCheckStale)
        XCTAssertFalse(store.needsAutomationNudge)
        XCTAssertTrue(store.dueWatches().isEmpty)

        let prompt = store.makeCheckPrompt(for: due)
        XCTAssertTrue(prompt.contains("PR"))
        XCTAssertTrue(prompt.contains("review comments"))
    }

    func testWatchIntervalDueMath() {
        let now = Date()
        var watch = AgentWatch(
            title: "x",
            prompt: "y",
            intervalHours: 2,
            lastCheckedAt: now.addingTimeInterval(-7200),
            createdAt: now
        )
        XCTAssertTrue(watch.isDue(at: now))
        watch.lastCheckedAt = now.addingTimeInterval(-3600)
        XCTAssertFalse(watch.isDue(at: now))
        watch.isPaused = true
        XCTAssertFalse(watch.isDue(at: now))
    }

    @MainActor
    func testConversationDumpIncludesHiddenToolResults() throws {
        let runtime = AgentRuntime()
        runtime.appendToolCall(name: "searchContacts", arguments: "Mom")
        runtime.appendToolResult(name: "searchContacts", result: "Mom <mom@example.com>")

        let visible = runtime.transcript.filter(\.isVisibleInChat)
        XCTAssertEqual(visible.count, runtime.transcript.filter { $0.kind != .toolResult }.count)
        XCTAssertTrue(visible.contains { entry in
            if case .toolCall(let name) = entry.kind {
                return name == "searchContacts" && entry.text == "Invoking searchContacts…"
            }
            return false
        })
        XCTAssertFalse(visible.contains { entry in
            if case .toolResult = entry.kind { return true }
            return false
        })

        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.entries.count, runtime.transcript.count)
        let result = try XCTUnwrap(dump.entries.first { $0.kind == "toolResult" })
        XCTAssertEqual(result.debugDetail, "Mom <mom@example.com>")
        let data = try runtime.conversationDumpJSONData()
        XCTAssertFalse(data.isEmpty)
        let url = try runtime.writeConversationDumpFile()
        defer { try? FileManager.default.removeItem(at: url) }
        XCTAssertTrue(FileManager.default.fileExists(atPath: url.path))
    }

    @MainActor
    func testBrowserOpenAcceptsHTTPSAndRejectsDemoSchemes() throws {
        let context = AgentToolContext()
        let loaded = try AgentToolExecutor.browserOpen(
            context: context,
            urlString: "https://example.com/path"
        )
        XCTAssertTrue(loaded.contains("example.com"))
        XCTAssertEqual(context.browserURL?.host, "example.com")

        XCTAssertThrowsError(
            try AgentToolExecutor.browserOpen(context: context, urlString: "file:///tmp/x.html")
        )
        XCTAssertThrowsError(
            try AgentToolExecutor.browserOpen(context: context, urlString: "not a url")
        )
    }
}
