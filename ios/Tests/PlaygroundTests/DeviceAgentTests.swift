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
        XCTAssertEqual(
            visible.count,
            runtime.transcript.filter { entry in
                if case .toolResult = entry.kind { return false }
                return true
            }.count
        )
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
        // Help text may already be in the transcript; ensure a toolCall is visible and a toolResult is not.
        XCTAssertTrue(runtime.transcript.contains { entry in
            if case .toolResult = entry.kind { return !entry.isVisibleInChat }
            return false
        })

        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.entries.count, runtime.transcript.count)
        let result = try XCTUnwrap(dump.entries.first { $0.kind == "toolResult" })
        XCTAssertEqual(result.debugDetail, "Mom <mom@example.com>")
        XCTAssertEqual(dump.browserReplay, runtime.context.browser.replay)
        let data = try runtime.conversationDumpJSONData()
        XCTAssertFalse(data.isEmpty)
        let url = try runtime.writeConversationDumpFile()
        defer { try? FileManager.default.removeItem(at: url) }
        XCTAssertTrue(FileManager.default.fileExists(atPath: url.path))
    }

    @MainActor
    func testPageFindingsBulletsAndReplayRecording() async {
        let bullets = AgentBrowserSession.pageFindingsBullets(
            from: """
            NFL Schedule 2026
            Week 1 opens with the kickoff game on Thursday night.
            Cookie settings Accept all
            Standings update after each Sunday slate.
            """,
            limit: 5
        )
        XCTAssertFalse(bullets.isEmpty)
        XCTAssertFalse(bullets.contains(where: { $0.lowercased().contains("cookie") }))

        let findings = AgentBrowserSession.pageFindingsText(
            title: "NFL Schedule",
            url: "https://www.espn.com/nfl/schedule",
            pageText: "Random filler that should rank below headings.",
            headings: ["NFL Schedule"],
            listItems: ["Week 1: Chiefs vs Ravens", "Week 2: Bills at Jets"]
        )
        XCTAssertTrue(findings.contains("From the page · NFL Schedule"))
        XCTAssertTrue(findings.contains("Week 1: Chiefs vs Ravens"))
        XCTAssertTrue(findings.contains("follow-up"))

        let headingFirst = AgentBrowserSession.pageFindingsBullets(
            headings: ["Standings"],
            listItems: ["AFC East leaders"],
            pageText: "This long body sentence should not displace the heading bullets from the page content itself.",
            limit: 3
        )
        XCTAssertEqual(headingFirst.first, "Standings")
        XCTAssertTrue(headingFirst.contains("AFC East leaders"))

        let prompt = AgentPageExtractor.buildPrompt(
            from: AgentPageExtractor.Input(
                userQuestion: "What's on the NFL schedule?",
                title: "NFL Schedule",
                url: "https://www.espn.com/nfl/schedule",
                headings: ["Week 1"],
                listItems: ["Chiefs vs Ravens"],
                pageText: "Thursday night kickoff"
            )
        )
        XCTAssertTrue(prompt.contains("User question:"))
        XCTAssertTrue(prompt.contains("NFL schedule"))
        XCTAssertTrue(prompt.contains("Chiefs vs Ravens"))

        AgentPageExtractor.testExtractionOverride = { input in
            XCTAssertEqual(input.userQuestion, "Summarize this schedule")
            return ["Week 1: Chiefs vs Ravens", "Week 2: Bills at Jets"]
        }
        defer { AgentPageExtractor.testExtractionOverride = nil }

        let runtime = AgentRuntime()
        runtime.lastUserPrompt = "Summarize this schedule"
        runtime.context.browser.record(
            action: "open",
            detail: "https://example.com",
            url: "https://example.com",
            title: "Example"
        )
        runtime.context.browser.record(
            action: "snapshot",
            detail: "2 elements",
            url: "https://example.com",
            title: "Example",
            pageText: "Hello from the page with enough text to become a bullet point here.",
            elements: [#"[1] link "Home""#],
            headings: ["Example"],
            listItems: ["Hello from the page"]
        )
        let enriched = try await runtime.appendToolResultAndEnrich(
            name: "browserSnapshot",
            result: "title: Example\nurl: https://example.com\ntext:\nHello from the page with enough text to become a bullet point here."
        )
        XCTAssertTrue(runtime.transcript.contains { $0.kind == .pageFindings })
        let pageCard = runtime.transcript.first { $0.kind == .pageFindings }?.text ?? ""
        XCTAssertTrue(pageCard.contains("From the page"))
        XCTAssertTrue(pageCard.contains("Week 1: Chiefs vs Ravens"))
        XCTAssertTrue(enriched.contains("extractedFindings"))
        XCTAssertTrue(enriched.contains("Week 1: Chiefs vs Ravens"))
        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.browserReplay.count, 2)
        XCTAssertEqual(dump.browserReplay.first?.action, "open")
        XCTAssertEqual(dump.browserReplay.last?.action, "snapshot")
        XCTAssertEqual(dump.browserReplay.last?.pageText?.contains("Hello from the page"), true)
    }

    @MainActor
    func testPageExtractionFailureIsVisibleAndThrows() async {
        AgentPageExtractor.testExtractionOverride = { _ in
            throw AgentPageExtractor.ExtractionError.emptyFindings
        }
        defer { AgentPageExtractor.testExtractionOverride = nil }

        let runtime = AgentRuntime()
        runtime.lastUserPrompt = "What games are on?"
        runtime.context.browser.record(
            action: "snapshot",
            detail: "0 elements",
            url: "https://example.com",
            title: "Example",
            pageText: "Nav only"
        )

        do {
            _ = try await runtime.appendToolResultAndEnrich(
                name: "browserSnapshot",
                result: "title: Example\ntext:\nNav only"
            )
            XCTFail("Expected page extraction to fail the tool")
        } catch {
            // expected
        }

        let failureCard = runtime.transcript.first { $0.kind == .pageFindings }?.text ?? ""
        XCTAssertTrue(failureCard.contains("Page extraction failed"))
        XCTAssertTrue(failureCard.contains("no page findings") || failureCard.lowercased().contains("failed"))
    }

    @MainActor
    func testBrowserOpenRejectsNonHTTP() async {
        let context = AgentToolContext()
        do {
            _ = try await AgentToolExecutor.browserOpen(context: context, urlString: "file:///tmp/x.html")
            XCTFail("Expected file URL to be rejected")
        } catch {
            // expected
        }
        do {
            _ = try await AgentToolExecutor.browserOpen(context: context, urlString: "not a url")
            XCTFail("Expected invalid URL to be rejected")
        } catch {
            // expected
        }
    }

    func testBrowserSnapshotFormattingAndJSEscape() {
        let raw = """
        {"title":"Example","url":"https://example.com/","elements":["[1] link \\"Home\\"","[2] textbox \\"Search\\""],"text":"Welcome"}
        """
        let formatted = AgentBrowserSession.formatSnapshotPayload(raw)
        XCTAssertTrue(formatted.contains("title: Example"))
        XCTAssertTrue(formatted.contains("url: https://example.com/"))
        XCTAssertTrue(formatted.contains("[1] link"))
        XCTAssertTrue(formatted.contains("text:"))
        XCTAssertTrue(formatted.contains("Welcome"))

        XCTAssertEqual(AgentBrowserSession.jsString("a'b"), "'a\\'b'")
        XCTAssertTrue(AgentBrowserSession.bridgeJavaScript.contains("__deviceAgent"))
        XCTAssertTrue(AgentBrowserSession.bridgeJavaScript.contains("snapshot"))
    }

    @MainActor
    func testBrowserRequireOKParsesFailure() {
        XCTAssertThrowsError(try AgentBrowserSession.requireOK(
            #"{"ok":false,"error":"unknown ref 9"}"#,
            action: "click"
        ))
        XCTAssertEqual(
            try AgentBrowserSession.requireOK(#"{"ok":true}"#, action: "click"),
            "click ok"
        )
    }
}
