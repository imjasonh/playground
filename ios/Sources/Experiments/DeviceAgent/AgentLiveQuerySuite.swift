import Foundation

/// A real user-style prompt for CI / Simulator soak testing.
struct AgentLiveQuery: Identifiable, Equatable {
    var id: String
    var prompt: String
    /// Short note about what capability this query is meant to stress.
    var stress: String
    /// When true, a clarifying location ask without browsing can still pass
    /// (no device GPS; model may ask for a city).
    var allowsClarifyingAskWithoutBrowse: Bool

    init(
        id: String,
        prompt: String,
        stress: String,
        allowsClarifyingAskWithoutBrowse: Bool = false
    ) {
        self.id = id
        self.prompt = prompt
        self.stress = stress
        self.allowsClarifyingAskWithoutBrowse = allowsClarifyingAskWithoutBrowse
    }
}

enum AgentLiveQueryStatus: String, Equatable {
    case completed
    case timedOut
    case failed
    case skipped
}

/// Outcome of one live query (non-deterministic content; scored on browse progress).
struct AgentLiveQueryResult: Identifiable, Equatable {
    var id: String { query.id }
    var query: AgentLiveQuery
    var status: AgentLiveQueryStatus
    /// True when the run finished with a usable reply and real browser work
    /// (or an allowed clarifying ask for near-me).
    var passed: Bool
    var toolCallCount: Int
    var browserToolCallCount: Int
    var pageFindingCount: Int
    var toolNames: [String]
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
            stress: "near-me without device location",
            allowsClarifyingAskWithoutBrowse: true
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
    static let browserToolNames: Set<String> = [
        "browserOpen", "browserRead", "browserSnapshot", "browserFind",
        "browserClick", "browserClickText", "browserType", "browserSelect",
        "browserGet", "browserScroll", "browserBack",
    ]

    struct Snapshot: Equatable {
        var toolCallCount: Int
        var browserToolCallCount: Int
        var pageFindingCount: Int
        var toolNames: [String]
        var assistantTexts: [String]
        var systemTexts: [String]
        var toolResultSnippets: [String]

        var assistantSnippet: String {
            String((assistantTexts.last ?? "").prefix(180))
        }

        var openedHTTPURL: Bool {
            toolResultSnippets.contains { snippet in
                let lower = snippet.lowercased()
                return lower.contains("https://") || lower.contains("http://")
            } || toolNames.contains("browserOpen")
        }

        @MainActor
        static func capture(from runtime: AgentRuntime, afterIndex: Int) -> Snapshot {
            let slice = Array(runtime.transcript.dropFirst(afterIndex))
            var tools = 0
            var browserTools = 0
            var findings = 0
            var names: [String] = []
            var assistants: [String] = []
            var systems: [String] = []
            var resultSnippets: [String] = []
            for entry in slice {
                switch entry.kind {
                case .toolCall(let name):
                    tools += 1
                    names.append(name)
                    if browserToolNames.contains(name) {
                        browserTools += 1
                    }
                    if let detail = entry.debugDetail, !detail.isEmpty {
                        resultSnippets.append(detail)
                    }
                case .toolResult(let name):
                    let detail = entry.debugDetail ?? ""
                    if !detail.isEmpty {
                        resultSnippets.append("\(name): \(detail)")
                    }
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
                browserToolCallCount: browserTools,
                pageFindingCount: findings,
                toolNames: names,
                assistantTexts: assistants,
                systemTexts: systems,
                toolResultSnippets: resultSnippets
            )
        }
    }

    static func looksLikeClarifyingAsk(_ text: String) -> Bool {
        let lower = text.lowercased()
        let needles = [
            "what city", "which city", "where are you", "your location",
            "near where", "share a city", "tell me a city", "what area",
            "zip code", "which neighborhood", "assume san francisco",
        ]
        return needles.contains { lower.contains($0) }
    }

    static func looksLikeHardFailure(_ text: String) -> Bool {
        let lower = text.lowercased()
        if lower.contains("(empty model response.)") { return true }
        if lower.hasPrefix("couldn't finish after compacting") { return true }
        if lower.contains("couldn't talk to that page") { return true }
        if lower.contains("took too long to load") { return true }
        if lower.contains("ran out of context") { return true }
        return false
    }

    /// Pass when the model finished with a reply and real browser tool use
    /// (or an allowed clarifying ask for near-me queries).
    static func passed(
        status: AgentLiveQueryStatus,
        snapshot: Snapshot,
        allowsClarifyingAskWithoutBrowse: Bool = false
    ) -> Bool {
        guard status == .completed else { return false }
        let reply = snapshot.assistantTexts.last ?? ""
        guard !reply.isEmpty, !looksLikeHardFailure(reply) else { return false }
        if snapshot.systemTexts.contains(where: looksLikeHardFailure) { return false }

        if allowsClarifyingAskWithoutBrowse, looksLikeClarifyingAsk(reply) {
            return true
        }

        // Must actually drive the in-app browser — a lone chat reply is not enough.
        guard snapshot.browserToolCallCount >= 1 else { return false }
        // Prefer evidence of a loaded page: findings card, open URL, or a multi-step dig.
        if snapshot.pageFindingCount >= 1 { return true }
        if snapshot.openedHTTPURL, reply.count >= 40 { return true }
        if snapshot.browserToolCallCount >= 2, reply.count >= 40 { return true }
        return false
    }
}

/// Drives live prompts through `AgentRuntime` so Foundation Models chooses tools against the real web.
///
/// Runs **sequentially**: all runtimes share `AgentBrowserSession.shared` (one WKWebView),
/// so parallel opens would race. Unit tests are the primary soak path.
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

    /// Optional launch argument for manual Simulator soaks (unit tests call `runAll` directly).
    static let launchArgument = "-deviceAgentLiveQueries"
    /// Back-compat with the first suite flag.
    static let legacyLaunchArgument = "-deviceAgentBrowserTasks"

    static var shouldAutostartFromLaunchArguments: Bool {
        let args = ProcessInfo.processInfo.arguments
        return args.contains(launchArgument) || args.contains(legacyLaunchArgument)
    }

    func runAll(
        runtime: AgentRuntime,
        suiteTimeoutSeconds: TimeInterval = 5 * 60,
        perQueryTimeoutSeconds: TimeInterval = 45
    ) async {
        guard !isRunning else { return }
        isRunning = true
        results = []
        skippedReason = nil
        summaryLine = "Running \(AgentLiveQueryCatalog.count) live queries…"
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
                    browserToolCallCount: 0,
                    pageFindingCount: 0,
                    toolNames: [],
                    assistantSnippet: "",
                    summary: "Skipped — \(runtime.modelStatusText)",
                    durationMs: 0
                )
            }
            results = skipped
            summaryLine = "0/\(AgentLiveQueryCatalog.count) passed (model unavailable)"
            return
        }

        let catalog = AgentLiveQueryCatalog.all
        let deadline = Date().addingTimeInterval(suiteTimeoutSeconds)
        var collected: [AgentLiveQueryResult] = []

        for (index, query) in catalog.enumerated() {
            let remaining = deadline.timeIntervalSinceNow
            if remaining <= 3 {
                for leftover in catalog[index...] {
                    collected.append(
                        AgentLiveQueryResult(
                            query: leftover,
                            status: .timedOut,
                            passed: false,
                            toolCallCount: 0,
                            browserToolCallCount: 0,
                            pageFindingCount: 0,
                            toolNames: [],
                            assistantSnippet: "",
                            summary: "Suite budget exhausted before this query.",
                            durationMs: 0
                        )
                    )
                }
                break
            }

            let queryBudget = min(perQueryTimeoutSeconds, max(5, remaining - 1))
            // Shared WKWebView: reuse one runtime so tabs do not race across queries.
            let result = await runOne(
                query,
                runtime: runtime,
                timeoutSeconds: queryBudget
            )
            collected.append(result)
            results = collected
            summaryLine = "\(collected.filter(\.passed).count)/\(collected.count) finished…"
        }

        results = collected
        summaryLine = "\(passedCount)/\(AgentLiveQueryCatalog.count) passed"
    }

    func reportText() -> String {
        var lines: [String] = [summaryLine]
        if let skippedReason {
            lines.append("Skip reason: \(skippedReason)")
        }
        for result in results {
            let mark = result.passed ? "PASS" : "FAIL"
            let tools = result.toolNames.isEmpty ? "-" : result.toolNames.joined(separator: ",")
            lines.append(
                "\(mark) \(result.query.id) [\(result.status.rawValue)] tools=\(result.toolCallCount) browser=\(result.browserToolCallCount) findings=\(result.pageFindingCount) \(result.durationMs)ms [\(tools)] — \(result.summary)"
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
        runtime.clearTranscript()
        // Drop prior tab so the next prompt must open a real page.
        AgentBrowserSession.shared.resetForNextQuery()
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
                browserToolCallCount: 0,
                pageFindingCount: 0,
                toolNames: [],
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

        let ok = AgentLiveQueryScorer.passed(
            status: effectiveStatus,
            snapshot: snapshot,
            allowsClarifyingAskWithoutBrowse: query.allowsClarifyingAskWithoutBrowse
        )
        let summary: String
        if ok {
            summary = "Completed with \(snapshot.browserToolCallCount) browser tool(s), \(snapshot.pageFindingCount) finding card(s)."
        } else if timedOut {
            summary = "Timed out after \(Int(timeoutSeconds))s (browserTools=\(snapshot.browserToolCallCount))."
        } else if snapshot.browserToolCallCount == 0 {
            summary = "Finished without browsing (no browser tool calls)."
        } else {
            summary = "Finished but browse evidence looked weak (browserTools=\(snapshot.browserToolCallCount), findings=\(snapshot.pageFindingCount))."
        }

        return AgentLiveQueryResult(
            query: query,
            status: effectiveStatus,
            passed: ok,
            toolCallCount: snapshot.toolCallCount,
            browserToolCallCount: snapshot.browserToolCallCount,
            pageFindingCount: snapshot.pageFindingCount,
            toolNames: snapshot.toolNames,
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
        await withTaskGroup(of: Bool.self) { group in
            group.addTask { @MainActor in
                await sendTask.value
                return false
            }
            group.addTask {
                let ns = UInt64(max(1, timeoutSeconds) * 1_000_000_000)
                try? await Task.sleep(nanoseconds: ns)
                return true
            }
            let first = await group.next() ?? true
            group.cancelAll()
            return first
        }
    }

    private func waitUntilIdle(runtime: AgentRuntime, maxSeconds: TimeInterval) async {
        let deadline = Date().addingTimeInterval(maxSeconds)
        while runtime.isRunning, Date() < deadline {
            try? await Task.sleep(nanoseconds: 200_000_000)
        }
    }
}
