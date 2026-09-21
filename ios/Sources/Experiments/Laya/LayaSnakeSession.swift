import Foundation

@MainActor
final class LayaSnakeSession: ObservableObject {
    typealias Predictor = @MainActor (String, LayaQuestion) async throws -> LayaPrediction

    @Published private(set) var game: LayaSnakeGame
    @Published private(set) var decision: LayaSnakeDecision?
    @Published private(set) var isRunning = false
    @Published private(set) var isDeciding = false
    @Published private(set) var failure: LayaFailure?
    @Published private(set) var round = 1
    @Published private(set) var best = 0
    @Published private(set) var interventions = 0
    @Published private(set) var inferenceCalls = 0
    /// Decisions per second over the last few steps of the current run.
    @Published private(set) var stepsPerSecond: Double = 0
    /// Wall time this round has spent running, in seconds.
    @Published private(set) var elapsed: TimeInterval = 0
    @Published private(set) var inferenceStats: LayaLatencyStats?

    /// Target decisions per second while paced.
    @Published var targetRate: Double = 6
    @Published var maxSpeed = false
    /// Restrict executed moves to cycle-safe progress; off runs raw top-1.
    @Published var guarded = true {
        didSet { if guarded != oldValue { note("shield \(guarded ? "on" : "off")") } }
    }

    static let rateRange: ClosedRange<Double> = 1...30
    static let windowSize = 20
    static let inferenceSampleLimit = 600

    private let predictor: Predictor
    private let note: @MainActor (String) -> Void
    private var task: Task<Void, Never>?
    private var recentSteps: [Date] = []
    private var inferenceSamples: [TimeInterval] = []

    init(seed: Int = 7, predictor: @escaping Predictor, note: @escaping @MainActor (String) -> Void = { _ in }) {
        game = LayaSnakeGame.standard(seed: seed)
        self.predictor = predictor
        self.note = note
    }

    var statusText: String {
        if let failure { return "Stopped: \(failure.message)" }
        if game.won { return "Board clear" }
        if !game.alive { return "Game over: \(game.deathReason?.rawValue ?? "collision")" }
        if isRunning { return "Live" }
        return game.ticks == 0 ? "Ready" : "Paused"
    }

    var fillFraction: Double {
        Double(game.body.count) / Double(game.capacity)
    }

    // MARK: Control

    func toggle() {
        if isRunning { pause() } else { start() }
    }

    func start() {
        guard !isRunning, !game.finished else { return }
        failure = nil
        isRunning = true
        recentSteps = []
        note("snake round \(round) \(game.ticks == 0 ? "started" : "resumed") at tick \(game.ticks), target \(Int(targetRate))/s\(maxSpeed ? " (max speed)" : ""), shield \(guarded ? "on" : "off")")
        task = Task { [weak self] in
            await self?.run()
        }
    }

    func pause() {
        task?.cancel()
        task = nil
        isRunning = false
        recentSteps = []
        stepsPerSecond = 0
    }

    func stepOnce() async {
        guard !isRunning, !isDeciding, !game.finished else { return }
        await step()
    }

    func nextRound() {
        pause()
        if game.ticks > 0 {
            note(summaryLine)
        }
        round += 1
        game = LayaSnakeGame.standard(seed: game.seed + 1)
        decision = nil
        failure = nil
        elapsed = 0
        interventions = 0
        inferenceCalls = 0
        inferenceSamples = []
        inferenceStats = nil
    }

    private func run() async {
        while !Task.isCancelled, !game.finished, failure == nil {
            let started = Date()
            await step()
            let spent = Date().timeIntervalSince(started)
            elapsed += spent
            if Task.isCancelled || game.finished || failure != nil { break }
            if !maxSpeed {
                let remaining = 1 / targetRate - spent
                if remaining > 0 {
                    do {
                        try await Task.sleep(for: .seconds(remaining))
                        elapsed += remaining
                    } catch {
                        break
                    }
                }
            }
        }
        if isRunning, game.finished || failure != nil {
            isRunning = false
            note(summaryLine)
        }
    }

    // MARK: One decision

    private func step() async {
        isDeciding = true
        defer { isDeciding = false }
        let started = Date()
        do {
            let turn = try LayaSnakePolicy.turn(for: game, guarded: guarded)
            let move = try await predictor(turn.state, turn.moveQuestion)
            let risk = try await predictor(turn.state, turn.riskQuestion)
            let food = try await predictor(turn.state, turn.foodQuestion)
            inferenceCalls += 3
            var decided = try LayaSnakePolicy.decision(
                turn: turn, move: move.decision, risk: risk.decision, food: food.decision, guarded: guarded
            )
            let predictions = [move, risk, food]
            decided.inferenceSeconds = predictions.reduce(0) { $0 + $1.timings.total }
            decided.graphSeconds = predictions.reduce(0) { $0 + $1.timings.graph }
            decided.inputTokens = predictions.reduce(0) { $0 + $1.inputTokens }
            decided.decisionSeconds = Date().timeIntervalSince(started)
            decision = decided

            try game.step(decided.executed)
            if decided.intervened { interventions += 1 }
            best = max(best, game.score)
            recordRate()
            recordInference(decided.inferenceSeconds)
            if !game.alive {
                note("snake died: \(game.deathReason?.rawValue ?? "collision") after \(game.ticks) ticks; proposed \(decided.proposed.rawValue), executed \(decided.executed.rawValue)")
            }
        } catch {
            let failure = LayaFailure(stage: "snake", error: error)
            self.failure = failure
            note("snake FAILED at tick \(game.ticks): " + failure.report.replacingOccurrences(of: "\n", with: " | "))
        }
    }

    private func recordRate() {
        let now = Date()
        recentSteps.append(now)
        if recentSteps.count > Self.windowSize {
            recentSteps.removeFirst(recentSteps.count - Self.windowSize)
        }
        guard recentSteps.count >= 2, let first = recentSteps.first else {
            stepsPerSecond = 0
            return
        }
        let span = now.timeIntervalSince(first)
        stepsPerSecond = span > 0 ? Double(recentSteps.count - 1) / span : 0
    }

    private func recordInference(_ seconds: TimeInterval) {
        inferenceSamples.append(seconds)
        if inferenceSamples.count > Self.inferenceSampleLimit {
            inferenceSamples.removeFirst(inferenceSamples.count - Self.inferenceSampleLimit)
        }
        inferenceStats = LayaLatencyStats(inferenceSamples)
    }

    // MARK: Report

    var summaryLine: String {
        var parts = [
            "snake round \(round): \(game.won ? "board clear" : game.alive ? "paused" : "died (\(game.deathReason?.rawValue ?? "collision"))")",
            "score \(game.score)", "length \(game.body.count)/\(game.capacity)", "\(game.ticks) ticks",
            "\(inferenceCalls) inference calls", "\(interventions) shield interventions",
            "\(LayaFormat.seconds(elapsed)) elapsed",
        ]
        if let inferenceStats {
            parts.append("inference per move median \(LayaFormat.seconds(inferenceStats.median)) p95 \(LayaFormat.seconds(inferenceStats.p95))")
        }
        return parts.joined(separator: ", ")
    }
}
