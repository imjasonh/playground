import Foundation

/// A real user-style prompt for CI / Simulator soak testing.
struct AgentLiveQuery: Identifiable, Equatable {
    var id: String
    var prompt: String
    /// Short note about what capability this query is meant to stress.
    var stress: String
}

enum AgentLiveQueryStatus: String, Equatable {
    case completed
    case timedOut
    case failed
    case skipped
}

/// Outcome of one live query (non-deterministic content; scored on progress).
struct AgentLiveQueryResult: Identifiable, Equatable {
    var id: String { query.id }
    var query: AgentLiveQuery
    var status: AgentLiveQueryStatus
    /// True when the run finished with a usable reply and real browser work (or a clear clarifying ask).
    var passed: Bool
    var toolCallCount: Int
    var pageFindingCount: Int
    var assistantSnippet: String
    var summary: String
    var durationMs: Int
}

/// Open-ended queries that exercise Device Agent against live websites.
enum AgentLiveQueryCatalog {
    static let all: [AgentLiveQuery] = [
        AgentLiveQuery(
            id: "ebike-top5",
            prompt: "Find me 5 high rated ebikes and their prices. Use the web; list model, rough price, and where you saw it.",
            stress: "multi-result shopping scrape"
        ),
        AgentLiveQuery(
            id: "radishes-near-me",
            prompt: "Where can I buy radishes near me?",
            stress: "near-me without device location"
        ),
        AgentLiveQuery(
            id: "macbook-price-compare",
            prompt: "Compare the current price of a 13-inch MacBook Air with M3 at Apple’s site and one major retailer. Quote the numbers you find.",
            stress: "cross-site price comparison"
        ),
        AgentLiveQuery(
            id: "bbc-headlines",
            prompt: "What are the top headlines on BBC News right now? Give me 4 short bullets from the page.",
            stress: "news homepage extraction"
        ),
        AgentLiveQuery(
            id: "wikipedia-facts",
            prompt: "Open the Wikipedia page for Ada Lovelace and give me three concrete facts taken from that page.",
            stress: "article read + cite page"
        ),
        AgentLiveQuery(
            id: "cookie-recipe",
            prompt: "Find a simple chocolate chip cookie recipe and list the ingredients with amounts from the page you opened.",
            stress: "recipe site navigation"
        ),
        AgentLiveQuery(
            id: "chicago-weekend-weather",
            prompt: "What’s the weather forecast for Chicago this weekend? Summarize highs and conditions from a weather site.",
            stress: "forecast lookup"
        ),
        AgentLiveQuery(
            id: "portland-vegetarian",
            prompt: "Find three vegetarian restaurants in Portland, Oregon and list a name and address for each from the web.",
            stress: "local business search with city given"
        ),
        AgentLiveQuery(
            id: "dune-scores",
            prompt: "Look up the movie Dune: Part Two and tell me its release year and critic score from a review aggregator or Wikipedia.",
            stress: "movie metadata lookup"
        ),
        AgentLiveQuery(
            id: "warriors-schedule",
            prompt: "Are the Golden State Warriors playing today? If not, when is their next game? Use a sports site and cite what you see.",
            stress: "sports schedule / conditional answer"
        ),
    ]

    static var count: Int { all.count }
}

/// Scores a transcript slice after one `AgentRuntime.send` without requiring fixed page text.
enum AgentLiveQueryScorer {
    struct Snapshot: Equatable {
        var toolCallCount: Int
        var pageFindingCount: Int
        var assistantTexts: [String]
        var systemTexts: [String]

        var assistantSnippet: String {
            String((assistantTexts.last ?? "").prefix(180))
        }

        @MainActor
        static func capture(from runtime: AgentRuntime, afterIndex: Int) -> Snapshot {
            let slice = Array(runtime.transcript.dropFirst(afterIndex))
            var tools = 0
            var findings = 0
            var assistants: [String] = []
            var systems: [String] = []
            for entry in slice {
                switch entry.kind {
                case .toolCall:
                    tools += 1
                case .pageFindings:
                    findings += 1
                    assistants.append(entry.text)
                case .assistant:
                    assistants.append(entry.text)
                case .system:
                    systems.append(entry.text)
                default:
                    break
                }
            }
            return Snapshot(
                toolCallCount: tools,
                pageFindingCount: findings,
                assistantTexts: assistants,
                systemTexts: systems
            )
        }
    }

    static func looksLikeClarifyingAsk(_ text: String) -> Bool {
        let lower = text.lowercased()
        let needles = [
            "what city", "which city", "where are you", "your location",
            "near where", "share a city", "tell me a city", "what area",
            "zip code", "which neighborhood",
        ]
        return needles.contains { lower.contains($0) }
    }

    static func looksLikeHardFailure(_ text: String) -> Bool {
        let lower = text.lowercased()
        if lower.contains("(empty model response.)") { return true }
        if lower.hasPrefix("couldn't finish after compacting") { return true }
        return false
    }

    /// Pass when the model finished with a reply and either browsed or clearly asked for location.
    static func passed(
        status: AgentLiveQueryStatus,
        snapshot: Snapshot
    ) -> Bool {
        guard status == .completed else { return false }
        let reply = snapshot.assistantTexts.last ?? ""
        guard !reply.isEmpty, !looksLikeHardFailure(reply) else { return false }
        if snapshot.toolCallCount >= 1 { return true }
        if looksLikeClarifyingAsk(reply) { return true }
        // Page findings without a separate assistant line still count as a usable answer.
        return snapshot.pageFindingCount >= 1 && reply.count >= 40
    }
}

/// Drives live prompts through `AgentRuntime` so Foundation Models chooses tools against the real web.
@MainActor
final class AgentLiveQueryRunner: ObservableObject {
    @Published private(set) var results: [AgentLiveQueryResult] = []
    @Published private(set) var isRunning = false
    @Published private(set) var summaryLine = ""
    @Published private(set) var skippedReason: String?

    var passedCount: Int { results.filter(\.passed).count }
    var completedCount: Int { results.filter { $0.status == .completed }.count }
    var totalCount: Int { results.count }
    var allPassed: Bool { !results.isEmpty && results.allSatisfy(\.passed) }

    /// Launch argument used by UI tests / CI.
    static let launchArgument = "-deviceAgentLiveQueries"
    /// Back-compat with the first suite flag.
    static let legacyLaunchArgument = "-deviceAgentBrowserTasks"

    static var shouldAutostartFromLaunchArguments: Bool {
        let args = ProcessInfo.processInfo.arguments
        return args.contains(launchArgument) || args.contains(legacyLaunchArgument)
    }

    func runAll(
        runtime: AgentRuntime,
        suiteTimeoutSeconds: TimeInterval = 5 * 60
    ) async {
        guard !isRunning else { return }
        isRunning = true
        results = []
        skippedReason = nil
        summaryLine = "Running \(AgentLiveQueryCatalog.count) live queries in parallel…"
        defer { isRunning = false }

        runtime.refreshModelStatus()
        guard runtime.isModelAvailable else {
            skippedReason = runtime.modelStatusText
            let skipped = AgentLiveQueryCatalog.all.map { query in
                AgentLiveQueryResult(
                    query: query,
                    status: .skipped,
                    passed: false,
                    toolCallCount: 0,
                    pageFindingCount: 0,
                    assistantSnippet: "",
                    summary: "Skipped — \(runtime.modelStatusText)",
                    durationMs: 0
                )
            }
            results = skipped
            summaryLine = "0/\(AgentLiveQueryCatalog.count) passed (model unavailable)"
            return
        }

        // One isolated runtime (transcript + WKWebView + model session) per query so
        // they can progress concurrently while awaiting network / AFM.
        let catalog = AgentLiveQueryCatalog.all
        var byID: [String: AgentLiveQueryResult] = [:]

        await withTaskGroup(of: AgentLiveQueryResult.self) { group in
            for query in catalog {
                group.addTask { @MainActor in
                    let isolated = AgentRuntime()
                    return await self.runOne(
                        query,
                        runtime: isolated,
                        timeoutSeconds: suiteTimeoutSeconds
                    )
                }
            }
            for await result in group {
                byID[result.query.id] = result
                let ordered = catalog.compactMap { byID[$0.id] }
                results = ordered
                summaryLine = "\(ordered.filter(\.passed).count)/\(ordered.count) finished…"
            }
        }

        results = catalog.compactMap { byID[$0.id] }
        summaryLine = "\(passedCount)/\(AgentLiveQueryCatalog.count) passed"
    }

    func reportText() -> String {
        var lines: [String] = [summaryLine]
        if let skippedReason {
            lines.append("Skip reason: \(skippedReason)")
        }
        for result in results {
            let mark = result.passed ? "PASS" : "FAIL"
            lines.append(
                "\(mark) \(result.query.id) [\(result.status.rawValue)] tools=\(result.toolCallCount) findings=\(result.pageFindingCount) \(result.durationMs)ms — \(result.summary)"
            )
            if !result.assistantSnippet.isEmpty {
                lines.append("  snippet: \(result.assistantSnippet.replacingOccurrences(of: "\n", with: " "))")
            }
        }
        return lines.joined(separator: "\n")
    }

    private func runOne(
        _ query: AgentLiveQuery,
        runtime: AgentRuntime,
        timeoutSeconds: TimeInterval
    ) async -> AgentLiveQueryResult {
        // Isolate context between open-ended queries.
        runtime.clearTranscript()
        let startIndex = runtime.transcript.count
        let started = Date()

        let sendTask = Task { @MainActor in
            await runtime.send(prompt: query.prompt, source: .chat)
        }

        let status: AgentLiveQueryStatus
        let timedOut = await waitForSend(
            sendTask: sendTask,
            timeoutSeconds: timeoutSeconds
        )
        if timedOut {
            status = .timedOut
            await waitUntilIdle(runtime: runtime, maxSeconds: 5)
        } else {
            status = .completed
        }

        let snapshot = AgentLiveQueryScorer.Snapshot.capture(from: runtime, afterIndex: startIndex)
        let durationMs = Int(Date().timeIntervalSince(started) * 1000)

        if snapshot.toolCallCount == 0,
           snapshot.assistantTexts.isEmpty,
           snapshot.pageFindingCount == 0 {
            let failedStatus: AgentLiveQueryStatus = timedOut ? .timedOut : .failed
            return AgentLiveQueryResult(
                query: query,
                status: failedStatus,
                passed: false,
                toolCallCount: 0,
                pageFindingCount: 0,
                assistantSnippet: "",
                summary: timedOut ? "Timed out with no reply." : "No assistant reply or tools.",
                durationMs: durationMs
            )
        }

        let effectiveStatus: AgentLiveQueryStatus = {
            if timedOut { return .timedOut }
            if let last = snapshot.assistantTexts.last, AgentLiveQueryScorer.looksLikeHardFailure(last) {
                return .failed
            }
            return status
        }()

        let ok = AgentLiveQueryScorer.passed(status: effectiveStatus, snapshot: snapshot)
        let summary: String
        if ok {
            summary = "Completed with \(snapshot.toolCallCount) tool call(s), \(snapshot.pageFindingCount) finding card(s)."
        } else if timedOut {
            summary = "Timed out after \(Int(timeoutSeconds))s (tools=\(snapshot.toolCallCount))."
        } else if snapshot.toolCallCount == 0 {
            summary = "Finished without browsing (no tool calls)."
        } else {
            summary = "Finished but reply looked unusable (tools=\(snapshot.toolCallCount))."
        }

        return AgentLiveQueryResult(
            query: query,
            status: effectiveStatus,
            passed: ok,
            toolCallCount: snapshot.toolCallCount,
            pageFindingCount: snapshot.pageFindingCount,
            assistantSnippet: snapshot.assistantSnippet,
            summary: summary,
            durationMs: durationMs
        )
    }

    /// Returns `true` if the timeout won before `send` finished.
    private func waitForSend(
        sendTask: Task<Void, Never>,
        timeoutSeconds: TimeInterval
    ) async -> Bool {
        let timeoutNs = UInt64(timeoutSeconds * 1_000_000_000)
        return await withTaskGroup(of: Bool.self) { group in
            group.addTask { @MainActor in
                await sendTask.value
                return false
            }
            group.addTask {
                try? await Task.sleep(nanoseconds: timeoutNs)
                return true
            }
            let first = await group.next() ?? false
            group.cancelAll()
            return first
        }
    }

    private func waitUntilIdle(runtime: AgentRuntime, maxSeconds: TimeInterval) async {
        let deadline = Date().addingTimeInterval(maxSeconds)
        while runtime.isRunning, Date() < deadline {
            try? await Task.sleep(nanoseconds: 250_000_000)
        }
    }
}
