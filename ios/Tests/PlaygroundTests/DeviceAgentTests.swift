import XCTest
@testable import Playground

final class DeviceAgentTests: XCTestCase {
    @MainActor
    override func setUp() async throws {
        try await super.setUp()
        AgentBrowserSession.shared.clearReplay()
        AgentPageExtractor.testExtractionOverride = nil
    }

    @MainActor
    override func tearDown() async throws {
        AgentPageExtractor.testExtractionOverride = nil
        AgentBrowserSession.shared.clearReplay()
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
    func testPageExtractionFailureFallsBackToApproximateFindings() async throws {
        AgentPageExtractor.testExtractionOverride = { _ in
            throw AgentPageExtractor.Failure(
                error: .emptyFindings(rawBulletCount: 2),
                rawModelBullets: [" ", "ok"]
            )
        }
        defer { AgentPageExtractor.testExtractionOverride = nil }

        let runtime = AgentRuntime()
        runtime.lastUserPrompt = "What do the ebikes cost?"
        runtime.context.browser.record(
            action: "snapshot",
            detail: "0 elements",
            url: "https://example.com/ebikes",
            title: "Ebike prices",
            pageText: "Trail Glide — $1,299\nCity Commuter — $899",
            headings: ["Ebike prices"],
            listItems: ["Trail Glide — $1,299", "City Commuter — $899"]
        )

        let enriched = try await runtime.appendToolResultAndEnrich(
            name: "browserSnapshot",
            result: "title: Ebike prices\ntext:\nTrail Glide — $1,299"
        )

        let failureCard = runtime.transcript.first { $0.kind == .pageFindings }?.text ?? ""
        XCTAssertTrue(failureCard.contains("Page extraction failed"))
        XCTAssertTrue(failureCard.contains("Approximate findings"))
        XCTAssertTrue(failureCard.contains("$1,299") || failureCard.contains("Trail Glide"))
        XCTAssertEqual(runtime.extractionDiagnostics.count, 1)
        let diagnostic = try XCTUnwrap(runtime.extractionDiagnostics.first)
        XCTAssertEqual(diagnostic.errorCode, "emptyFindings")
        XCTAssertEqual(diagnostic.userQuestion, "What do the ebikes cost?")
        XCTAssertEqual(diagnostic.url, "https://example.com/ebikes")
        XCTAssertFalse(runtime.cachedPageFindings.isEmpty)
        XCTAssertTrue(enriched.contains("approximateFindings") || enriched.contains("$1,299"))
        XCTAssertTrue(enriched.contains("AFM page extraction failed"))
        // Tool must stay usable for the model (no throw).
        XCTAssertTrue(enriched.contains("elements") || enriched.contains("title:"))

        let dump = runtime.makeConversationDump()
        XCTAssertEqual(dump.extractionDiagnostics.count, 1)
        let jsonl = try runtime.conversationDumpJSONLData()
        let text = try XCTUnwrap(String(data: jsonl, encoding: .utf8))
        XCTAssertTrue(text.contains(#""type":"extractionDiagnostic""#))
        XCTAssertTrue(text.contains("emptyFindings"))
        XCTAssertTrue(text.contains("What do the ebikes cost?"))
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

    func testErrorCopyMapsNetworkAndToolFailures() {
        let offline = NSError(
            domain: NSURLErrorDomain,
            code: NSURLErrorNotConnectedToInternet,
            userInfo: [NSLocalizedDescriptionKey: "offline"]
        )
        XCTAssertTrue(AgentErrorCopy.userMessage(for: offline).localizedCaseInsensitiveContains("network"))

        let timeout = AgentToolError.unavailable("Timed out loading https://example.com")
        XCTAssertTrue(AgentErrorCopy.userMessage(for: timeout).localizedCaseInsensitiveContains("long"))

        let click = AgentToolError.unavailable("browser click: unknown ref 9")
        XCTAssertTrue(AgentErrorCopy.userMessage(for: click).localizedCaseInsensitiveContains("browserFind"))
    }

    func testApproximatePriceFindingsPreferDollarLines() {
        let bullets = AgentBrowserSession.approximateFindings(
            userQuestion: "What do the ebikes cost?",
            headings: ["Shop"],
            listItems: ["Trail Glide — $1,299", "Accept all cookies"],
            pageText: "Nav\nCity Commuter — $899\nPrivacy policy"
        )
        XCTAssertTrue(bullets.contains(where: { $0.contains("$1,299") }))
        XCTAssertTrue(bullets.contains(where: { $0.contains("$899") }))
        XCTAssertFalse(bullets.contains(where: { $0.lowercased().contains("cookie") }))
    }

    func testLiveQueryCatalogHasTenOpenEndedPrompts() {
        XCTAssertEqual(AgentLiveQueryCatalog.count, 10)
        XCTAssertEqual(Set(AgentLiveQueryCatalog.all.map(\.id)).count, 10)
        for query in AgentLiveQueryCatalog.all {
            XCTAssertFalse(query.prompt.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty)
            XCTAssertGreaterThanOrEqual(query.prompt.split(separator: " ").count, 5)
        }
        XCTAssertTrue(AgentLiveQueryCatalog.all.contains { $0.prompt.localizedCaseInsensitiveContains("ebike") })
        XCTAssertTrue(AgentLiveQueryCatalog.all.contains { $0.prompt.localizedCaseInsensitiveContains("radish") })
    }

    func testLiveQueryScorerAcceptsBrowseOrClarifyingAsk() {
        let browsed = AgentLiveQueryScorer.Snapshot(
            toolCallCount: 2,
            pageFindingCount: 1,
            assistantTexts: ["• Trail Glide about $1,200 on Example Shop"],
            systemTexts: []
        )
        XCTAssertTrue(AgentLiveQueryScorer.passed(status: .completed, snapshot: browsed))

        let clarify = AgentLiveQueryScorer.Snapshot(
            toolCallCount: 0,
            pageFindingCount: 0,
            assistantTexts: ["What city should I search near?"],
            systemTexts: []
        )
        XCTAssertTrue(AgentLiveQueryScorer.passed(status: .completed, snapshot: clarify))
        XCTAssertTrue(AgentLiveQueryScorer.looksLikeClarifyingAsk("What city should I search near?"))

        let emptyBrowse = AgentLiveQueryScorer.Snapshot(
            toolCallCount: 0,
            pageFindingCount: 0,
            assistantTexts: ["Hello"],
            systemTexts: []
        )
        XCTAssertFalse(AgentLiveQueryScorer.passed(status: .completed, snapshot: emptyBrowse))
        XCTAssertFalse(AgentLiveQueryScorer.passed(status: .timedOut, snapshot: browsed))
    }
}
