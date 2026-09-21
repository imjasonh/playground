import SwiftUI
import UIKit

/// Snake played by the loaded model, after `laya-coreml-snake`: the board on
/// top, then the model's direction probabilities, risk and reachability
/// estimates, and the per-move timings.
struct LayaSnakeView: View {
    @ObservedObject var store: LayaModelStore
    @StateObject private var session: LayaSnakeSession
    @State private var copied = false

    init(store: LayaModelStore) {
        self.store = store
        _session = StateObject(wrappedValue: LayaSnakeSession(
            predictor: { state, question in
                try await store.predict(state: state, question: question, recording: false)
            },
            note: { store.note($0) }
        ))
    }

    private var game: LayaSnakeGame { session.game }

    var body: some View {
        Form {
            boardSection
            controlsSection
            if store.phase != .ready {
                Section {
                    Text("The model is not loaded. Load it on the Laya screen, then come back.")
                        .foregroundStyle(.secondary)
                }
            }
            if let failure = session.failure {
                failureSection(failure)
            }
            nextMoveSection
            performanceSection
            aboutSection
        }
        .navigationTitle("Snake")
        .navigationBarTitleDisplayMode(.inline)
        .onDisappear { session.pause() }
    }

    // MARK: Board

    private var boardSection: some View {
        Section {
            LayaSnakeBoard(game: game)
                .aspectRatio(CGFloat(game.width) / CGFloat(game.height), contentMode: .fit)
                .accessibilityIdentifier("layaSnakeBoard")
                .listRowInsets(EdgeInsets())
            HStack(alignment: .firstTextBaseline) {
                counter("Score", game.score, .green)
                counter("Length", game.body.count, .primary)
                counter("Best", session.best, .secondary)
                Spacer()
                VStack(alignment: .trailing, spacing: 2) {
                    Text(session.statusText)
                        .font(.subheadline.weight(.semibold))
                        .foregroundStyle(game.alive ? Color.green : Color.red)
                        .accessibilityIdentifier("layaSnakeStatus")
                    Text("Round \(session.round)")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
            }
            VStack(alignment: .leading, spacing: 4) {
                ProgressView(value: session.fillFraction)
                Text("\(game.body.count) of \(game.capacity) cells (\(LayaFormat.percent(session.fillFraction)))")
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }
        }
    }

    private func counter(_ title: String, _ value: Int, _ color: Color) -> some View {
        VStack(alignment: .leading, spacing: 0) {
            Text(title.uppercased())
                .font(.caption2)
                .foregroundStyle(.secondary)
            Text(String(format: "%03d", value))
                .font(.title2.monospacedDigit().weight(.semibold))
                .foregroundStyle(color)
        }
        .frame(minWidth: 64, alignment: .leading)
    }

    // MARK: Controls

    private var controlsSection: some View {
        Section("Controls") {
            HStack {
                Button {
                    session.toggle()
                } label: {
                    Label(
                        session.isRunning ? "Pause" : game.ticks == 0 ? "Play" : "Resume",
                        systemImage: session.isRunning ? "pause.fill" : "play.fill"
                    )
                }
                .buttonStyle(.borderedProminent)
                .disabled(game.finished || store.phase != .ready)
                .accessibilityIdentifier("layaSnakePlayButton")
                Button {
                    Task { await session.stepOnce() }
                } label: {
                    Label("Step", systemImage: "forward.frame")
                }
                .buttonStyle(.bordered)
                .disabled(session.isRunning || session.isDeciding || game.finished || store.phase != .ready)
                .accessibilityIdentifier("layaSnakeStepButton")
                Button {
                    session.nextRound()
                } label: {
                    Label("Next round", systemImage: "arrow.counterclockwise")
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("layaSnakeResetButton")
            }
            .buttonBorderShape(.capsule)
            VStack(alignment: .leading) {
                LabeledContent("Decisions per second") {
                    Text(session.maxSpeed ? "max" : "\(Int(session.targetRate))").monospacedDigit()
                }
                Slider(value: $session.targetRate, in: LayaSnakeSession.rateRange, step: 1)
                    .disabled(session.maxSpeed)
                    .accessibilityIdentifier("layaSnakeRateSlider")
            }
            Toggle("Max speed", isOn: $session.maxSpeed)
                .accessibilityIdentifier("layaSnakeMaxSpeedToggle")
            Toggle("Cycle safety shield", isOn: $session.guarded)
                .accessibilityIdentifier("layaSnakeShieldToggle")
        }
    }

    // MARK: Failure

    private func failureSection(_ failure: LayaFailure) -> some View {
        Section("Error") {
            Text(failure.message)
                .font(.callout)
                .foregroundStyle(.orange)
                .textSelection(.enabled)
                .accessibilityIdentifier("layaSnakeFailureMessage")
            ForEach(Array(failure.details.enumerated()), id: \.offset) { _, detail in
                Text(detail)
                    .font(.caption.monospaced())
                    .foregroundStyle(.secondary)
                    .textSelection(.enabled)
            }
            Button {
                UIPasteboard.general.string = failure.report
            } label: {
                Label("Copy error", systemImage: "doc.on.doc")
            }
        }
    }

    // MARK: Next move

    @ViewBuilder
    private var nextMoveSection: some View {
        Section("Next move") {
            if let decision = session.decision {
                ForEach(LayaSnakeDirection.allCases, id: \.rawValue) { direction in
                    directionRow(direction, decision)
                }
                LabeledContent("Executing") {
                    HStack(spacing: 8) {
                        Text(decision.executed.rawValue)
                            .font(.body.weight(.semibold))
                            .foregroundStyle(.green)
                        if decision.intervened {
                            Text("SHIELD")
                                .font(.caption2.weight(.bold))
                                .padding(.horizontal, 6)
                                .padding(.vertical, 2)
                                .background(Color.orange.opacity(0.2), in: Capsule())
                                .foregroundStyle(.orange)
                        }
                    }
                }
                if let planner = decision.plannerBest {
                    LabeledContent("Planner best", value: planner.rawValue)
                }
                estimateRow("Dead-end risk", decision.deadEndRisk, decision.deadEndRisk < 0.5 ? .orange : .red)
                estimateRow("Food reachable", decision.foodReachable, .cyan)
            } else {
                Text("Press Play or Step. The board shows the probabilities the model gave before each announced move.")
                    .foregroundStyle(.secondary)
            }
        }
    }

    private func directionRow(_ direction: LayaSnakeDirection, _ decision: LayaSnakeDecision) -> some View {
        let probability = decision.probabilities[direction] ?? 0
        let proposed = direction == decision.proposed
        let safe = decision.safeDirections.contains(direction)
        return VStack(alignment: .leading, spacing: 2) {
            HStack {
                Text(proposed ? "›" : " ")
                    .font(.body.monospaced().weight(.bold))
                    .foregroundStyle(.green)
                Text(direction.rawValue)
                    .font(.subheadline.monospaced())
                    .foregroundStyle(proposed ? .primary : .secondary)
                if !safe {
                    Text("unsafe")
                        .font(.caption2)
                        .foregroundStyle(.orange)
                }
                Spacer()
                Text(String(format: "%.2f", probability))
                    .font(.subheadline.monospacedDigit())
                    .foregroundStyle(proposed ? .primary : .secondary)
            }
            ProgressView(value: min(max(probability, 0), 1))
                .tint(proposed ? .green : .gray)
        }
    }

    private func estimateRow(_ title: String, _ value: Double, _ color: Color) -> some View {
        VStack(alignment: .leading, spacing: 2) {
            HStack {
                Text(title).font(.subheadline)
                Spacer()
                Text(String(format: "%.2f", value))
                    .font(.subheadline.monospacedDigit())
                    .foregroundStyle(.secondary)
            }
            ProgressView(value: min(max(value, 0), 1)).tint(color)
        }
    }

    // MARK: Performance

    @ViewBuilder
    private var performanceSection: some View {
        Section("Performance") {
            if let decision = session.decision {
                LabeledContent("Inference, 3 questions") {
                    Text(LayaFormat.seconds(decision.inferenceSeconds)).monospacedDigit()
                }
                LabeledContent("Of which MLModel.prediction") {
                    Text(LayaFormat.seconds(decision.graphSeconds)).monospacedDigit()
                }
                LabeledContent("Whole decision") {
                    Text(LayaFormat.seconds(decision.decisionSeconds)).monospacedDigit()
                }
                LabeledContent("Input tokens", value: "\(decision.inputTokens)")
            }
            if let stats = session.inferenceStats {
                LabeledContent("Inference median / p95") {
                    Text("\(LayaFormat.seconds(stats.median)) / \(LayaFormat.seconds(stats.p95))").monospacedDigit()
                }
            }
            LabeledContent("Decisions") {
                Text(String(format: "%.1f /s", session.stepsPerSecond)).monospacedDigit()
            }
            LabeledContent("Output tokens", value: "0")
            LabeledContent("Network", value: "Offline")
            LabeledContent("Engine", value: store.info?.computeUnits ?? "not loaded")
            LabeledContent("Inference calls", value: "\(session.inferenceCalls)")
            LabeledContent("Shield interventions", value: "\(session.interventions)")
            LabeledContent("Elapsed", value: Self.clock(session.elapsed))
            Button {
                UIPasteboard.general.string = summary
                copied = true
                Task {
                    try? await Task.sleep(for: .seconds(2))
                    copied = false
                }
            } label: {
                Label(copied ? "Copied" : "Copy round summary", systemImage: copied ? "checkmark" : "doc.on.doc")
            }
            .accessibilityIdentifier("layaSnakeCopySummary")
        }
    }

    private var summary: String {
        var lines = [session.summaryLine]
        if let decision = session.decision {
            let probabilities = LayaSnakeDirection.allCases
                .map { "\($0.rawValue) \(String(format: "%.3f", decision.probabilities[$0] ?? 0))" }
                .joined(separator: ", ")
            lines.append("last move: proposed \(decision.proposed.rawValue), executed \(decision.executed.rawValue)\(decision.intervened ? " (shield)" : ""); \(probabilities)")
            lines.append("last estimates: dead-end risk \(String(format: "%.3f", decision.deadEndRisk)), food reachable \(String(format: "%.3f", decision.foodReachable))")
            lines.append("last timings: inference \(LayaFormat.seconds(decision.inferenceSeconds)) (graph \(LayaFormat.seconds(decision.graphSeconds))), decision \(LayaFormat.seconds(decision.decisionSeconds)), \(decision.inputTokens) input tokens")
        }
        lines.append("engine: \(store.info?.computeUnits ?? "not loaded"); device: \(store.device.text)")
        return lines.joined(separator: "\n")
    }

    private static func clock(_ seconds: TimeInterval) -> String {
        let whole = Int(seconds)
        return String(format: "%02d:%02d", whole / 60, whole % 60)
    }

    // MARK: About

    private var aboutSection: some View {
        Section("About") {
            Text("Code computes legal moves, cycle-safe progress along a Hamiltonian cycle, and whether food is reachable through empty cells. Each move asks the model three questions about those features: which direction to take (choice), whether a safe route exists (yes/no), and whether food is reachable (yes/no). Dead-end risk is 1 − P(safe route).")
                .font(.footnote)
                .foregroundStyle(.secondary)
            Text("With the shield on, an unsafe top-1 pick is replaced by the most probable safe move and counted as an intervention; the raw probabilities stay on screen. With it off, the model's top-1 is executed as is, so the snake can die. The ANE bundle answers one question per pass, so a move costs three passes.")
                .font(.footnote)
                .foregroundStyle(.secondary)
            Link("Snake demo in laya-coreml", destination: LayaModelSource.snakeDocsURL)
        }
    }
}

/// The board, drawn with the terminal demo's palette.
struct LayaSnakeBoard: View {
    let game: LayaSnakeGame

    private static let background = Color(red: 9 / 255, green: 15 / 255, blue: 19 / 255)
    private static let dot = Color(red: 19 / 255, green: 39 / 255, blue: 46 / 255)
    private static let food = Color(red: 1, green: 206 / 255, blue: 115 / 255)
    private static let head = Color(red: 220 / 255, green: 1, blue: 240 / 255)

    var body: some View {
        Canvas { context, size in
            let cell = min(size.width / CGFloat(game.width), size.height / CGFloat(game.height))
            let origin = CGPoint(
                x: (size.width - cell * CGFloat(game.width)) / 2,
                y: (size.height - cell * CGFloat(game.height)) / 2
            )
            context.fill(Path(CGRect(origin: .zero, size: size)), with: .color(Self.background))

            func rect(_ at: LayaSnakeCell) -> CGRect {
                CGRect(x: origin.x + CGFloat(at.x) * cell, y: origin.y + CGFloat(at.y) * cell, width: cell, height: cell)
            }

            let dotRadius = max(0.75, cell * 0.06)
            for y in 0..<game.height {
                for x in 0..<game.width {
                    let center = CGPoint(x: origin.x + (CGFloat(x) + 0.5) * cell, y: origin.y + (CGFloat(y) + 0.5) * cell)
                    context.fill(
                        Path(ellipseIn: CGRect(x: center.x - dotRadius, y: center.y - dotRadius, width: dotRadius * 2, height: dotRadius * 2)),
                        with: .color(Self.dot)
                    )
                }
            }
            if let food = game.food {
                context.fill(Path(ellipseIn: rect(food).insetBy(dx: cell * 0.2, dy: cell * 0.2)), with: .color(Self.food))
            }
            let count = game.body.count
            for (index, segment) in game.body.enumerated().reversed() {
                let inset = max(0.5, cell * 0.08)
                let path = Path(roundedRect: rect(segment).insetBy(dx: inset, dy: inset), cornerRadius: cell * 0.2)
                context.fill(path, with: .color(Self.bodyColor(index: index, count: count)))
            }
        }
    }

    /// Head is near white; the body fades from bright to dark green toward the tail.
    static func bodyColor(index: Int, count: Int) -> Color {
        if index == 0 { return head }
        let fraction = 1 - Double(index) / Double(max(1, count))
        return Color(
            red: (18 + 64 * fraction) / 255,
            green: (73 + 150 * fraction) / 255,
            blue: (57 + 102 * fraction) / 255
        )
    }
}
