import XCTest
@testable import Playground

final class DeviceAgentTests: XCTestCase {
    @MainActor
    override func setUp() async throws {
        try await super.setUp()
        AgentBrowserSession.shared.clearReplay()
        AgentPageExtractor.testExtractionOverride = nil
        _ = AgentInbox.shared.consumePendingRun()
    }

    @MainActor
    override func tearDown() async throws {
        AgentPageExtractor.testExtractionOverride = nil
        AgentBrowserSession.shared.clearReplay()
        _ = AgentInbox.shared.consumePendingRun()
        try await super.tearDown()
    }

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
        await runtime.send(prompt: "open https://example.com", source: .chat)
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
        let url = URL(string: "playground://device-agent?prompt=hello%20world&voice=1")!
        let inbox = AgentInbox.shared
        XCTAssertTrue(inbox.handleOpenURL(url))
        let run = inbox.consumePendingRun()
        XCTAssertEqual(run?.prompt, "hello world")
        XCTAssertEqual(run?.preferVoice, true)
        XCTAssertEqual(run?.source, .deepLink)
        XCTAssertNil(run?.url)
    }

    @MainActor
    func testDeepLinkParsesURLAndPrompt() {
        let url = URL(
            string: "playground://device-agent?url=https%3A%2F%2Fexample.com%2Fdocs&prompt=find%20pricing"
        )!
        XCTAssertTrue(AgentInbox.shared.handleOpenURL(url))
        let run = AgentInbox.shared.consumePendingRun()
        XCTAssertEqual(run?.url, "https://example.com/docs")
        XCTAssertEqual(run?.prompt, "find pricing")
        XCTAssertEqual(run?.browserURL?.absoluteString, "https://example.com/docs")
        XCTAssertEqual(run?.source, .deepLink)
    }

    @MainActor
    func testEnqueueBrowserDriveStoresURL() {
        let page = URL(string: "https://example.com/a")!
        AgentInbox.shared.enqueueBrowserDrive(
            url: page,
            prompt: "Click Sign in",
            source: .shortcut
        )
        let run = AgentInbox.shared.consumePendingRun()
        XCTAssertEqual(run?.url, "https://example.com/a")
        XCTAssertEqual(run?.prompt, "Click Sign in")
        XCTAssertEqual(run?.source, .shortcut)
    }

    @MainActor
    func testIntentActionsAskAndBrowse() throws {
        let askMessage = DeviceAgentIntentActions.ask(prompt: "open example.com")
        XCTAssertTrue(askMessage.contains("Queued"))
        let askRun = AgentInbox.shared.consumePendingRun()
        XCTAssertEqual(askRun?.prompt, "open example.com")
        XCTAssertNil(askRun?.url)

        let browseMessage = try DeviceAgentIntentActions.browse(
            url: URL(string: "https://example.com")!,
            prompt: "Summarize pricing"
        )
        XCTAssertTrue(browseMessage.contains("https://example.com"))
        let browseRun = AgentInbox.shared.consumePendingRun()
        XCTAssertEqual(browseRun?.url, "https://example.com")
        XCTAssertEqual(browseRun?.prompt, "Summarize pricing")

        XCTAssertThrowsError(
            try DeviceAgentIntentActions.browse(url: URL(string: "ftp://example.com")!)
        )
    }

    func testResolvedPromptForBrowserDrive() {
        let withURL = AgentPendingRun(
            prompt: "find pricing",
            source: .shortcut,
            url: "https://example.com"
        )
        XCTAssertEqual(
            AgentPendingRun.resolvedPrompt(withURL, pageAlreadyOpen: false),
            "Open https://example.com and find pricing"
        )
        XCTAssertTrue(
            AgentPendingRun.resolvedPrompt(withURL, pageAlreadyOpen: true)
                .contains("find pricing")
        )

        let summarize = AgentPendingRun(prompt: "", source: .shortcut, url: "https://example.com")
        XCTAssertTrue(
            AgentPendingRun.resolvedPrompt(summarize, pageAlreadyOpen: false)
                .contains("Open https://example.com")
        )
        XCTAssertTrue(
            AgentPendingRun.resolvedPrompt(summarize, pageAlreadyOpen: true)
                .contains("browserSnapshot")
        )

        let chatOnly = AgentPendingRun(prompt: "hello", source: .chat)
        XCTAssertEqual(
            AgentPendingRun.resolvedPrompt(chatOnly, pageAlreadyOpen: false),
            "hello"
        )
        XCTAssertNil(chatOnly.browserURL)
        XCTAssertNil(
            AgentPendingRun(prompt: "", source: .shortcut, url: "ftp://example.com").browserURL
        )
    }

    @MainActor
    func testOpenURLIgnoresOtherSchemes() {
        let url = URL(string: "https://example.com")!
        XCTAssertFalse(AgentInbox.shared.handleOpenURL(url))
    }

    func testPermissionDomainPrePromptIsNonEmpty() {
        for domain in AgentPermissionDomain.allCases {
            XCTAssertFalse(domain.prePrompt.isEmpty)
            XCTAssertFalse(domain.title.isEmpty)
        }
        XCTAssertEqual(AgentPermissionDomain.allCases.count, 2)
    }

    @MainActor
    func testConversationDumpIncludesHiddenToolResults() throws {
        let runtime = AgentRuntime()
        runtime.appendToolCall(name: "browserSnapshot", arguments: "max=3500")
        runtime.appendToolResult(name: "browserSnapshot", result: "title: Example\ntext:\nHello")

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
                return name == "browserSnapshot" && entry.text == "Invoking browserSnapshot…"
            }
            return false
        })
        XCTAssertFalse(visible.contains { entry in
            if case .toolResult = entry.kind { return true }
            return false
        })
        XCTAssertTrue(runtime.transcript.contains { entry in
            if case .toolResult = entry.kind { return !entry.isVisibleInChat }
            return false
        })

        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.mode, "browser")
        XCTAssertEqual(dump.entries.count, runtime.transcript.count)
        let result = try XCTUnwrap(dump.entries.first { $0.kind == "toolResult" })
        XCTAssertEqual(result.debugDetail, "title: Example\ntext:\nHello")
        XCTAssertEqual(dump.browserReplay, runtime.context.browser.replay)
        XCTAssertEqual(dump.extractionDiagnostics, runtime.extractionDiagnostics)
        let jsonl = try runtime.conversationDumpJSONLData()
        XCTAssertFalse(jsonl.isEmpty)
        let jsonlText = try XCTUnwrap(String(data: jsonl, encoding: .utf8))
        XCTAssertTrue(jsonlText.contains(#""type":"meta""#))
        XCTAssertTrue(jsonlText.contains(#""type":"entry""#))
        let zip = try runtime.conversationDumpZipData()
        XCTAssertEqual(Array(zip.prefix(4)), [0x50, 0x4b, 0x03, 0x04])
        let url = try runtime.writeConversationDumpFile()
        defer { try? FileManager.default.removeItem(at: url) }
        XCTAssertTrue(url.lastPathComponent.hasSuffix(".jsonl.zip"))
        XCTAssertTrue(FileManager.default.fileExists(atPath: url.path))
    }

    @MainActor
    func testPageFindingsBulletsAndReplayRecording() async throws {
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
        // Model-facing payload must stay slim (no full page text dump).
        XCTAssertFalse(enriched.contains("Hello from the page with enough text"))
        XCTAssertTrue(enriched.contains("Page text omitted"))
        XCTAssertGreaterThan(runtime.contextUsage.windowTokens, 0)
        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.browserReplay.count, 2)
        XCTAssertEqual(dump.browserReplay.first?.action, "open")
        XCTAssertEqual(dump.browserReplay.last?.action, "snapshot")
        XCTAssertEqual(dump.browserReplay.last?.pageText?.contains("Hello from the page"), true)
    }

    @MainActor
    func testPageExtractionFailureIsVisibleAndThrows() async throws {
        AgentPageExtractor.testExtractionOverride = { _ in
            throw AgentPageExtractor.Failure(
                error: .emptyFindings(rawBulletCount: 2),
                rawModelBullets: [" ", "ok"]
            )
        }
        defer { AgentPageExtractor.testExtractionOverride = nil }

        let runtime = AgentRuntime()
        runtime.lastUserPrompt = "What games are on?"
        runtime.context.browser.record(
            action: "snapshot",
            detail: "0 elements",
            url: "https://example.com/nfl",
            title: "Example",
            pageText: "Nav only",
            headings: ["NFL"],
            listItems: ["Week 1"]
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
        XCTAssertTrue(failureCard.contains("Export the conversation ZIP"))
        XCTAssertEqual(runtime.extractionDiagnostics.count, 1)
        let diagnostic = try XCTUnwrap(runtime.extractionDiagnostics.first)
        XCTAssertEqual(diagnostic.errorCode, "emptyFindings")
        XCTAssertEqual(diagnostic.userQuestion, "What games are on?")
        XCTAssertEqual(diagnostic.url, "https://example.com/nfl")
        XCTAssertEqual(diagnostic.headings, ["NFL"])
        XCTAssertTrue(diagnostic.prompt.contains("User question:"))
        XCTAssertEqual(diagnostic.rawModelBullets, [" ", "ok"])
        XCTAssertNotNil(diagnostic.rawSnapshotPrefix)

        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.extractionDiagnostics.count, 1)
        let jsonl = try runtime.conversationDumpJSONLData()
        let text = try XCTUnwrap(String(data: jsonl, encoding: .utf8))
        XCTAssertTrue(text.contains(#""type":"extractionDiagnostic""#))
        XCTAssertTrue(text.contains("emptyFindings"))
        XCTAssertTrue(text.contains("What games are on?"))
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
        XCTAssertTrue(AgentBrowserSession.bridgeJavaScript.contains("__version === 3"))
        XCTAssertTrue(AgentBrowserSession.bridgeJavaScript.contains("clickText"))
        XCTAssertTrue(AgentBrowserSession.bridgeJavaScript.contains("find:"))
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
        XCTAssertEqual(
            try AgentBrowserSession.requireOK(
                #"{"ok":true,"detail":"clicked link \"Home\" (ref=3)"}"#,
                action: "clickText"
            ),
            #"clicked link "Home" (ref=3)"#
        )
    }

    func testBrowserFindAndGetFormatting() {
        let find = AgentBrowserSession.formatFindPayload(
            #"{"query":"bike","matches":["[3] link \"E-bike deals\"","[8] link \"Bike shop\""]}"#
        )
        XCTAssertTrue(find.contains("matches (2):"))
        XCTAssertTrue(find.contains("[3] link"))
        XCTAssertEqual(
            AgentBrowserSession.formatFindPayload(#"{"query":"zzz","matches":[]}"#),
            #"No matches for "zzz"."#
        )

        let get = AgentBrowserSession.formatGetPayload(
            #"{"ok":true,"ref":"3","kind":"link","label":"Home","href":"https://example.com/","value":""}"#
        )
        XCTAssertTrue(get.contains("ref=3"))
        XCTAssertTrue(get.contains("href=https://example.com/"))
        XCTAssertEqual(
            AgentBrowserSession.formatGetPayload(#"{"ok":false,"error":"unknown ref 9"}"#),
            "get failed: unknown ref 9"
        )
    }

    func testContextBudgetEstimatesAndTruncates() {
        XCTAssertEqual(AgentContextBudget.estimateTokens(""), 0)
        XCTAssertEqual(AgentContextBudget.estimateTokens("abc"), 1)
        XCTAssertEqual(AgentContextBudget.estimateTokens(String(repeating: "a", count: 12)), 4)

        var budget = AgentContextBudget()
        budget.resetBaseline(instructions: String(repeating: "i", count: 300), toolsReserveTokens: 900)
        XCTAssertGreaterThan(budget.fractionUsed, 0)
        XCTAssertLessThan(budget.fractionUsed, AgentContextBudget.compactThreshold)
        XCTAssertFalse(budget.needsCompact)

        budget.addTokens(2_500)
        XCTAssertTrue(budget.needsCompact)
        XCTAssertGreaterThanOrEqual(budget.percentUsed, 72)

        let truncated = AgentContextBudget.truncateToChars(String(repeating: "x", count: 100), maxChars: 20)
        XCTAssertEqual(truncated.count, 20)
        XCTAssertTrue(truncated.hasSuffix("…"))

        let slim = AgentContextBudget.modelFacingSnapshot(
            title: "Example",
            url: "https://example.com",
            elements: (1...50).map { "[\($0)] link \"Item \($0)\"" },
            headings: ["Hello"],
            extractedFindings: ["Fact one", "Fact two"],
            maxChars: 800
        )
        XCTAssertTrue(slim.contains("extractedFindings"))
        XCTAssertTrue(slim.contains("Fact one"))
        XCTAssertTrue(slim.contains("showing 40"))
        XCTAssertLessThanOrEqual(slim.count, 800)
        // 40 element lines push past 800 chars, so the footer is truncated.
        XCTAssertTrue(slim.hasSuffix("…"))
        XCTAssertFalse(slim.contains("Page text omitted"))

        let roomy = AgentContextBudget.modelFacingSnapshot(
            title: "Example",
            url: "https://example.com",
            elements: ["[1] link \"Home\""],
            headings: ["Hello"],
            extractedFindings: ["Fact one"],
            maxChars: 2_000
        )
        XCTAssertTrue(roomy.contains("Page text omitted"))

        let carry = AgentContextBudget.compactionCarryOver(
            url: "https://example.com",
            title: "Example",
            findings: ["A", "B"],
            findingsURL: "https://example.com",
            recentUserPrompts: ["first", "second", "third", "fourth"]
        )
        XCTAssertTrue(carry.contains("https://example.com"))
        XCTAssertTrue(carry.contains("• A"))
        XCTAssertTrue(carry.contains("fourth"))
        XCTAssertFalse(carry.contains("- first"))

        let stale = AgentContextBudget.compactionCarryOver(
            url: "https://example.com/b",
            title: "B",
            findings: ["Old page fact"],
            findingsURL: "https://example.com/a",
            recentUserPrompts: ["what is on this page?"]
        )
        XCTAssertTrue(stale.contains("https://example.com/b"))
        XCTAssertFalse(stale.contains("Old page fact"))
        XCTAssertFalse(stale.contains("Latest page findings"))
    }

    func testContextBudgetSnapshotCharBudgetShrinksWhenFull() {
        var budget = AgentContextBudget()
        budget.resetBaseline(instructions: "short", toolsReserveTokens: 100)
        let roomy = budget.snapshotTextCharBudget()
        XCTAssertGreaterThanOrEqual(roomy, 400)

        budget.addTokens(3_200)
        let tight = budget.snapshotTextCharBudget()
        XCTAssertLessThan(tight, roomy)
        XCTAssertGreaterThanOrEqual(tight, 400)
        XCTAssertTrue(budget.isNearHardStop || budget.needsCompact)
    }

    @MainActor
    func testBrowserOpenClearsCachedPageFindings() async throws {
        AgentPageExtractor.testExtractionOverride = { _ in ["From page A"] }
        defer { AgentPageExtractor.testExtractionOverride = nil }

        let runtime = AgentRuntime()
        runtime.lastUserPrompt = "facts?"
        runtime.context.browser.record(
            action: "snapshot",
            detail: "1",
            url: "https://example.com/a",
            title: "A",
            pageText: "Hello A",
            elements: [#"[1] link "Home""#],
            headings: ["A"],
            listItems: []
        )
        _ = try await runtime.appendToolResultAndEnrich(
            name: "browserSnapshot",
            result: "title: A\ntext:\nHello A"
        )
        XCTAssertEqual(runtime.cachedPageFindings, ["From page A"])
        XCTAssertEqual(runtime.cachedPageFindingsURL, "https://example.com/a")

        _ = try await runtime.appendToolResultAndEnrich(
            name: "browserOpen",
            result: "Loaded https://example.com/b in the in-app browser. Call browserSnapshot next."
        )
        XCTAssertTrue(runtime.cachedPageFindings.isEmpty)
        XCTAssertNil(runtime.cachedPageFindingsURL)
    }

    func testExceededContextWindowDetection() {
        let err = NSError(
            domain: "FoundationModels.LanguageModelSession.GenerationError",
            code: -1,
            userInfo: [NSLocalizedDescriptionKey: "Exceeded model context window size"]
        )
        XCTAssertTrue(AgentRuntime.isExceededContextWindow(err))

        let bareCode = NSError(
            domain: "FoundationModels.LanguageModelSession.GenerationError",
            code: -1,
            userInfo: [
                NSLocalizedDescriptionKey:
                    "The operation couldn’t be completed. (FoundationModels.LanguageModelSession.GenerationError error -1.)",
            ]
        )
        XCTAssertTrue(AgentRuntime.isExceededContextWindow(bareCode))

        XCTAssertFalse(AgentRuntime.isExceededContextWindow(
            NSError(domain: "test", code: 1, userInfo: [NSLocalizedDescriptionKey: "network down"])
        ))
    }

    @MainActor
    func testRuntimePublishesContextUsage() async throws {
        let runtime = AgentRuntime()
        XCTAssertEqual(runtime.contextUsage.windowTokens, AgentContextBudget.defaultWindowTokens)
        XCTAssertGreaterThanOrEqual(runtime.contextUsage.percentUsed, 0)

        AgentPageExtractor.testExtractionOverride = { _ in ["Bullet"] }
        defer { AgentPageExtractor.testExtractionOverride = nil }
        runtime.lastUserPrompt = "hi"
        runtime.context.browser.record(
            action: "snapshot",
            detail: "1",
            url: "https://example.com",
            title: "Example",
            pageText: "Hello",
            elements: [#"[1] link "Home""#],
            headings: ["Example"],
            listItems: []
        )
        let before = runtime.contextUsage.usedTokens
        _ = try await runtime.appendToolResultAndEnrich(
            name: "browserSnapshot",
            result: "title: Example\ntext:\nHello"
        )
        XCTAssertGreaterThan(runtime.contextUsage.usedTokens, before)
        XCTAssertFalse(runtime.contextUsage.accessibilityLabel.isEmpty)
    }
}
