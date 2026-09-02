import Foundation

/// One real-site browse scenario for CI soak (no AFM tool selection required).
struct AgentLiveBrowseScenario: Identifiable, Equatable {
    var id: String
    /// User-facing question this scenario stands in for.
    var prompt: String
    /// Concrete http(s) URL the in-app browser must open.
    var url: String
    /// Case-insensitive substrings; at least one must appear in snapshot/page text.
    var contentNeedles: [String]
    /// Optional find query to exercise browserFind after snapshot.
    var findQuery: String?
}

enum AgentLiveBrowseStatus: String, Equatable {
    case completed
    case failed
}

struct AgentLiveBrowseResult: Identifiable, Equatable {
    var id: String { scenario.id }
    var scenario: AgentLiveBrowseScenario
    var status: AgentLiveBrowseStatus
    var passed: Bool
    var openDetail: String
    var snapshotChars: Int
    var findDetail: String
    var summary: String
    var durationMs: Int
}

/// Real websites corresponding to the open-ended Device Agent prompts.
/// Driven through `AgentToolExecutor` so CI exercises WKWebView loads/scrapes
/// without relying on Foundation Models tool selection (unsupported on most
/// Simulator / GHA hosts even when Simulated AFM Availability is enabled).
enum AgentLiveBrowseCatalog {
    static let all: [AgentLiveBrowseScenario] = [
        AgentLiveBrowseScenario(
            id: "ebike-top5",
            prompt: "Find me 5 high rated ebikes and their prices.",
            url: "https://duckduckgo.com/html/?q=best+rated+ebikes+prices",
            contentNeedles: ["bike", "ebike", "electric", "price", "$"],
            findQuery: "price"
        ),
        AgentLiveBrowseScenario(
            id: "radishes-near-me",
            prompt: "Where can I buy radishes near me?",
            url: "https://duckduckgo.com/html/?q=buy+radishes+San+Francisco",
            contentNeedles: ["radish", "produce", "market", "grocery", "francisco"],
            findQuery: "radish"
        ),
        AgentLiveBrowseScenario(
            id: "macbook-price-compare",
            prompt: "Compare MacBook Air M3 prices.",
            url: "https://www.apple.com/macbook-air/",
            contentNeedles: ["MacBook", "Air", "Apple"],
            findQuery: "MacBook"
        ),
        AgentLiveBrowseScenario(
            id: "bbc-headlines",
            prompt: "What are the top headlines on BBC News?",
            url: "https://www.bbc.com/news",
            contentNeedles: ["BBC", "News", "World"],
            findQuery: "News"
        ),
        AgentLiveBrowseScenario(
            id: "wikipedia-facts",
            prompt: "Open Ada Lovelace on Wikipedia and cite facts.",
            url: "https://en.wikipedia.org/wiki/Ada_Lovelace",
            contentNeedles: ["Lovelace", "Ada", "Babbage", "computer"],
            findQuery: "Lovelace"
        ),
        AgentLiveBrowseScenario(
            id: "cookie-recipe",
            prompt: "Find a chocolate chip cookie recipe.",
            url: "https://duckduckgo.com/html/?q=simple+chocolate+chip+cookie+recipe+ingredients",
            contentNeedles: ["cookie", "chocolate", "flour", "sugar", "recipe"],
            findQuery: "cookie"
        ),
        AgentLiveBrowseScenario(
            id: "chicago-weekend-weather",
            prompt: "Chicago weekend weather forecast.",
            url: "https://duckduckgo.com/html/?q=Chicago+weekend+weather+forecast",
            contentNeedles: ["chicago", "weather", "forecast", "°", "temp"],
            findQuery: "weather"
        ),
        AgentLiveBrowseScenario(
            id: "portland-vegetarian",
            prompt: "Vegetarian restaurants in Portland, Oregon.",
            url: "https://duckduckgo.com/html/?q=vegetarian+restaurants+Portland+Oregon",
            contentNeedles: ["portland", "vegetarian", "vegan", "restaurant"],
            findQuery: "vegetarian"
        ),
        AgentLiveBrowseScenario(
            id: "dune-scores",
            prompt: "Dune: Part Two release year and critic score.",
            url: "https://en.wikipedia.org/wiki/Dune:_Part_Two",
            contentNeedles: ["Dune", "2024", "Villeneuve", "film"],
            findQuery: "2024"
        ),
        AgentLiveBrowseScenario(
            id: "warriors-schedule",
            prompt: "Golden State Warriors next game.",
            url: "https://duckduckgo.com/html/?q=Golden+State+Warriors+schedule",
            contentNeedles: ["warrior", "golden state", "nba", "schedule", "game"],
            findQuery: "Warriors"
        ),
    ]

    static var count: Int { all.count }
}

/// Opens real URLs in the shared WKWebView and asserts scrape progress.
@MainActor
final class AgentLiveBrowseSoakRunner: ObservableObject {
    @Published private(set) var results: [AgentLiveBrowseResult] = []
    @Published private(set) var isRunning = false
    @Published private(set) var summaryLine = ""

    var passedCount: Int { results.filter(\.passed).count }
    var totalCount: Int { results.count }
    var allPassed: Bool { !results.isEmpty && results.allSatisfy(\.passed) }

    static let launchArgument = "-deviceAgentLiveQueries"
    static let legacyLaunchArgument = "-deviceAgentBrowserTasks"

    static var shouldAutostartFromLaunchArguments: Bool {
        let args = ProcessInfo.processInfo.arguments
        return args.contains(launchArgument) || args.contains(legacyLaunchArgument)
    }

    func runAll(
        context: AgentToolContext = AgentToolContext(),
        suiteTimeoutSeconds: TimeInterval = 5 * 60,
        perScenarioTimeoutSeconds: TimeInterval = 40
    ) async {
        guard !isRunning else { return }
        isRunning = true
        results = []
        summaryLine = "Running \(AgentLiveBrowseCatalog.count) live browse soaks…"
        defer { isRunning = false }

        let catalog = AgentLiveBrowseCatalog.all
        let deadline = Date().addingTimeInterval(suiteTimeoutSeconds)
        var collected: [AgentLiveBrowseResult] = []

        for (index, scenario) in catalog.enumerated() {
            let remaining = deadline.timeIntervalSinceNow
            if remaining <= 3 {
                for leftover in catalog[index...] {
                    collected.append(
                        AgentLiveBrowseResult(
                            scenario: leftover,
                            status: .failed,
                            passed: false,
                            openDetail: "",
                            snapshotChars: 0,
                            findDetail: "",
                            summary: "Suite budget exhausted before this scenario.",
                            durationMs: 0
                        )
                    )
                }
                break
            }

            let budget = min(perScenarioTimeoutSeconds, max(8, remaining - 1))
            let result = await runOne(scenario, context: context, timeoutSeconds: budget)
            collected.append(result)
            results = collected
            summaryLine = "\(collected.filter(\.passed).count)/\(collected.count) finished…"
        }

        results = collected
        summaryLine = "\(passedCount)/\(AgentLiveBrowseCatalog.count) passed"
    }

    func reportText() -> String {
        var lines: [String] = [summaryLine]
        for result in results {
            let mark = result.passed ? "PASS" : "FAIL"
            lines.append(
                "\(mark) \(result.scenario.id) [\(result.status.rawValue)] snap=\(result.snapshotChars) \(result.durationMs)ms — \(result.summary)"
            )
            if !result.openDetail.isEmpty {
                lines.append("  open: \(result.openDetail.prefix(160))")
            }
            if !result.findDetail.isEmpty {
                lines.append("  find: \(result.findDetail.prefix(120))")
            }
        }
        return lines.joined(separator: "\n")
    }

    private func runOne(
        _ scenario: AgentLiveBrowseScenario,
        context: AgentToolContext,
        timeoutSeconds: TimeInterval
    ) async -> AgentLiveBrowseResult {
        AgentBrowserSession.shared.resetForNextQuery()
        context.browserURL = nil
        context.browserTitle = ""
        let started = Date()

        let work = Task { @MainActor in
            try await Self.execute(scenario, context: context)
        }

        let timedOut: Bool = await withTaskGroup(of: Bool.self) { group in
            group.addTask { @MainActor in
                _ = await work.result
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

        if timedOut {
            work.cancel()
            return AgentLiveBrowseResult(
                scenario: scenario,
                status: .failed,
                passed: false,
                openDetail: "",
                snapshotChars: 0,
                findDetail: "",
                summary: "Timed out after \(Int(timeoutSeconds))s opening/scraping \(scenario.url).",
                durationMs: Int(Date().timeIntervalSince(started) * 1000)
            )
        }

        switch await work.result {
        case .success(let outcome):
            return AgentLiveBrowseResult(
                scenario: scenario,
                status: outcome.passed ? .completed : .failed,
                passed: outcome.passed,
                openDetail: outcome.openDetail,
                snapshotChars: outcome.snapshotChars,
                findDetail: outcome.findDetail,
                summary: outcome.summary,
                durationMs: Int(Date().timeIntervalSince(started) * 1000)
            )
        case .failure(let error):
            return AgentLiveBrowseResult(
                scenario: scenario,
                status: .failed,
                passed: false,
                openDetail: "",
                snapshotChars: 0,
                findDetail: "",
                summary: AgentErrorCopy.userMessage(for: error),
                durationMs: Int(Date().timeIntervalSince(started) * 1000)
            )
        }
    }

    private struct Outcome {
        var passed: Bool
        var openDetail: String
        var snapshotChars: Int
        var findDetail: String
        var summary: String
    }

    private static func execute(
        _ scenario: AgentLiveBrowseScenario,
        context: AgentToolContext
    ) async throws -> Outcome {
        let openDetail = try await AgentToolExecutor.browserOpen(
            context: context,
            urlString: scenario.url
        )
        let snapshot = try await AgentToolExecutor.browserSnapshot(
            context: context,
            maxTextChars: 8_000
        )
        var findDetail = ""
        if let query = scenario.findQuery, !query.isEmpty {
            findDetail = try await AgentToolExecutor.browserFind(context: context, query: query)
        }

        let haystack = (snapshot + "\n" + findDetail + "\n" + (context.browser.title)).lowercased()
        let matched = scenario.contentNeedles.contains { needle in
            haystack.contains(needle.lowercased())
        }

        // Approximate findings path should still surface something useful on shop/search pages.
        let approx = AgentBrowserSession.approximateFindings(
            userQuestion: scenario.prompt,
            pageText: snapshot,
            limit: 8
        )
        let hasSignal = matched
            || snapshot.count >= 200
            || !approx.isEmpty
            || findDetail.localizedCaseInsensitiveContains("match")

        let summary: String
        if hasSignal && matched {
            summary = "Loaded and matched content (\(snapshot.count) snap chars, approx=\(approx.count))."
        } else if hasSignal {
            summary = "Loaded page but needles missed (snap=\(snapshot.count), approx=\(approx.count))."
        } else {
            summary = "Weak scrape after open (snap=\(snapshot.count))."
        }

        return Outcome(
            passed: hasSignal && matched,
            openDetail: openDetail,
            snapshotChars: snapshot.count,
            findDetail: findDetail,
            summary: summary
        )
    }
}
