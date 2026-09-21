import SwiftUI
import UIKit

/// Download the Laya ANE bundle, then ask it typed questions about a text.
///
/// Uses ``LayaModelStore/shared`` so a download here is the same graph Army
/// List uses.
///
/// Every stage reports its timing, every failure is copyable with its
/// underlying error chain, and **Copy report** gathers all of it for a
/// TestFlight round trip.
struct LayaView: View {
    @ObservedObject private var store = LayaModelStore.shared
    @State private var draft = LayaDraft.examples[0]
    @State private var prediction: LayaPrediction?
    @State private var failure: LayaFailure?
    @State private var copied: String?

    var body: some View {
        Form {
            modelSection
            if let failure = store.phase.failure {
                failureSection(failure)
            }
            if store.phase == .ready {
                performanceSection
                questionSection
                resultSection
                benchmarkSection
                demosSection
            }
            diagnosticsSection
            deviceSection
            aboutSection
        }
        .navigationTitle("Laya")
        .navigationBarTitleDisplayMode(.inline)
        .task {
            if store.isDownloaded {
                await store.prepare()
            }
        }
    }

    // MARK: Model

    private var modelSection: some View {
        Section("Model") {
            statusRow
            Picker("Compute units", selection: $store.computeChoice) {
                ForEach(LayaComputeChoice.allCases) { choice in
                    Text(choice.title).tag(choice)
                }
            }
            .disabled(store.phase.isBusy)
            .accessibilityIdentifier("layaComputePicker")
            switch store.phase {
            case .notDownloaded, .failed:
                Button {
                    Task { await store.prepare() }
                } label: {
                    Label(
                        store.isDownloaded ? "Load model" : "Download model (\(LayaModelSource.sizeText))",
                        systemImage: store.isDownloaded ? "cpu" : "arrow.down.circle"
                    )
                }
                .accessibilityIdentifier("layaDownloadButton")
            case .downloading(let fraction):
                ProgressView(value: fraction)
                    .accessibilityIdentifier("layaDownloadProgress")
            case .verifying, .compiling, .loading:
                ProgressView()
            case .ready:
                if let info = store.info {
                    LabeledContent("Revision", value: info.revision)
                    LabeledContent("Sequence", value: "\(info.sequenceLength) tokens × \(info.maxOptions) slots")
                    LabeledContent("Width", value: "\(info.width), vocab \(info.vocabularySize), \(info.hostWeightsDType)")
                    LabeledContent("Compute", value: info.computeUnits)
                }
                Button("Unload model") {
                    prediction = nil
                    store.unload()
                }
                .accessibilityIdentifier("layaUnloadButton")
            }
            if store.isDownloaded, !store.phase.isBusy {
                Button("Delete download", role: .destructive) {
                    prediction = nil
                    store.deleteModel()
                }
                .accessibilityIdentifier("layaDeleteButton")
            }
        }
    }

    private var statusRow: some View {
        HStack {
            Image(systemName: statusSymbol)
                .foregroundStyle(statusColor)
            Text(statusText)
        }
        .font(.subheadline)
        .accessibilityIdentifier("layaStatus")
    }

    private var statusText: String {
        switch store.phase {
        case .notDownloaded:
            return store.isDownloaded ? "Downloaded, not loaded" : "Not downloaded"
        case .downloading(let fraction):
            return "Downloading \(Int(fraction * 100))%"
        case .verifying: return "Verifying checksums"
        case .compiling: return "Compiling for this device"
        case .loading: return "Loading"
        case .ready:
            return LayaModelStore.isSimulator ? "Ready (Simulator: CPU only)" : "Ready"
        case .failed(let failure): return "Failed during \(failure.stage)"
        }
    }

    private var statusSymbol: String {
        switch store.phase {
        case .ready: return "checkmark.circle.fill"
        case .failed: return "exclamationmark.triangle.fill"
        case .notDownloaded: return "circle.dashed"
        default: return "hourglass"
        }
    }

    private var statusColor: Color {
        switch store.phase {
        case .ready: return .green
        case .failed: return .orange
        default: return .secondary
        }
    }

    // MARK: Failure

    private func failureSection(_ failure: LayaFailure) -> some View {
        Section("Error") {
            Text(failure.message)
                .font(.callout)
                .foregroundStyle(.orange)
                .textSelection(.enabled)
                .accessibilityIdentifier("layaFailureMessage")
            ForEach(Array(failure.details.enumerated()), id: \.offset) { _, detail in
                Text(detail)
                    .font(.caption.monospaced())
                    .foregroundStyle(.secondary)
                    .textSelection(.enabled)
            }
            copyButton("Copy error", id: "layaCopyError") { failure.report }
        }
    }

    // MARK: Performance

    @ViewBuilder
    private var performanceSection: some View {
        Section("Load performance") {
            ForEach(store.stages) { stage in
                LabeledContent(stage.name.capitalized) {
                    VStack(alignment: .trailing) {
                        Text(LayaFormat.seconds(stage.seconds)).monospacedDigit()
                        if let note = stage.note {
                            Text(note).font(.caption2).foregroundStyle(.secondary)
                        }
                    }
                }
            }
            if let memory = store.loadMemory {
                LabeledContent("Resident memory", value: "\(LayaFormat.bytes(memory.before)) → \(LayaFormat.bytes(memory.after))")
            }
            if let plan = store.computePlan {
                Text(plan.headline)
                    .font(.subheadline)
                    .accessibilityIdentifier("layaComputePlanHeadline")
                ForEach(Array(plan.deviceRows.enumerated()), id: \.offset) { _, row in
                    LabeledContent(row.device, value: "\(row.operations) ops · cost \(LayaFormat.percent(row.cost))")
                }
                if plan.unplanned > 0 {
                    LabeledContent("No device reported", value: "\(plan.unplanned) ops")
                }
                if !plan.fallbackRows.isEmpty {
                    Text("Off Neural Engine: " + plan.fallbackRows.prefix(12).map { "\($0.operator)×\($0.count)" }.joined(separator: ", "))
                        .font(.caption.monospaced())
                        .foregroundStyle(.secondary)
                        .textSelection(.enabled)
                }
            }
            Button {
                Task { await store.analyzeComputePlan() }
            } label: {
                if store.isPlanning {
                    ProgressView()
                } else {
                    Label(store.computePlan == nil ? "Analyze compute plan" : "Re-analyze compute plan", systemImage: "cpu")
                }
            }
            .disabled(store.isPlanning)
            .accessibilityIdentifier("layaComputePlanButton")
        }
    }

    // MARK: Question

    private var questionSection: some View {
        Section("Question") {
            Picker("Type", selection: $draft.kind) {
                ForEach(LayaQuestionKind.allCases, id: \.self) { kind in
                    Text(kind.displayName).tag(kind)
                }
            }
            .pickerStyle(.segmented)
            .accessibilityIdentifier("layaKindPicker")

            VStack(alignment: .leading, spacing: 4) {
                Text("State").font(.caption).foregroundStyle(.secondary)
                TextEditor(text: $draft.state)
                    .frame(minHeight: 88)
                    .font(.body)
                    .accessibilityIdentifier("layaStateEditor")
            }

            TextField("Instructions", text: $draft.instructions, axis: .vertical)
                .accessibilityIdentifier("layaInstructionsField")

            switch draft.kind {
            case .choice:
                TextField("Options, one per line (label: description)", text: $draft.options, axis: .vertical)
                    .lineLimit(2...8)
                    .accessibilityIdentifier("layaOptionsField")
            case .score:
                TextField("Levels, one per line", text: $draft.options, axis: .vertical)
                    .lineLimit(2...8)
                    .accessibilityIdentifier("layaOptionsField")
            case .noul:
                EmptyView()
            }

            Menu("Load an example") {
                ForEach(LayaDraft.examples) { example in
                    Button(example.title) {
                        draft = example
                        prediction = nil
                        failure = nil
                    }
                }
            }

            if let tokenBudgetText {
                Text(tokenBudgetText)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("layaTokenBudget")
            }

            Button {
                Task { await ask() }
            } label: {
                if store.isPredicting, !store.isBenchmarking {
                    ProgressView()
                } else {
                    Label("Ask", systemImage: "sparkles")
                }
            }
            .disabled(store.isPredicting || store.isBenchmarking)
            .accessibilityIdentifier("layaAskButton")

            if let failure {
                Text(failure.message)
                    .font(.footnote)
                    .foregroundStyle(.orange)
                    .textSelection(.enabled)
                    .accessibilityIdentifier("layaError")
                ForEach(Array(failure.details.enumerated()), id: \.offset) { _, detail in
                    Text(detail)
                        .font(.caption2.monospaced())
                        .foregroundStyle(.secondary)
                        .textSelection(.enabled)
                }
                copyButton("Copy error", id: "layaCopyAskError") { failure.report }
            }
        }
    }

    /// `"<used> / <limit> tokens"` for the current draft, or nil until the
    /// model is loaded or when the draft is not a valid question yet.
    private var tokenBudgetText: String? {
        guard let limit = store.maxTokens,
              let question = try? draft.question(),
              case .success(let used)? = store.tokenCount(state: draft.state, question: question)
        else { return nil }
        return "\(used) / \(limit) tokens"
    }

    // MARK: Result

    @ViewBuilder
    private var resultSection: some View {
        if let prediction {
            Section("Answer") {
                LayaDecisionBars(decision: prediction.decision)
                LabeledContent("Act probability", value: LayaFormat.percent(prediction.decision.actProbability))
                LabeledContent("Input tokens", value: "\(prediction.inputTokens)")
            }
            .accessibilityIdentifier("layaResult")
            Section("Latency") {
                ForEach(Array(prediction.timings.rows.enumerated()), id: \.offset) { _, row in
                    LabeledContent(row.name.capitalized, value: LayaFormat.seconds(row.seconds))
                        .monospacedDigit()
                        .font(row.name == "total" ? .body.bold() : .body)
                }
                if let graph = store.graphStats, graph.count > 1 {
                    LabeledContent("Graph, last \(graph.count)", value: "median \(LayaFormat.seconds(graph.median)) · p95 \(LayaFormat.seconds(graph.p95))")
                        .font(.footnote)
                }
                if let total = store.totalStats, total.count > 1 {
                    LabeledContent("Total, last \(total.count)", value: "median \(LayaFormat.seconds(total.median)) · p95 \(LayaFormat.seconds(total.p95))")
                        .font(.footnote)
                }
                Text(prediction.outputSummary)
                    .font(.caption2.monospaced())
                    .foregroundStyle(.secondary)
                    .textSelection(.enabled)
            }
            .accessibilityIdentifier("layaLatency")
        }
    }

    // MARK: Demos

    private var demosSection: some View {
        Section("Demos") {
            NavigationLink {
                LayaSnakeView(store: store)
            } label: {
                Label("Snake", systemImage: "gamecontroller")
            }
            .accessibilityIdentifier("layaSnakeLink")
        }
    }

    // MARK: Benchmark

    private var benchmarkSection: some View {
        Section("Benchmark") {
            Button {
                Task {
                    guard let question = try? draft.question() else { return }
                    await store.runBenchmark(state: draft.state, question: question)
                }
            } label: {
                if store.isBenchmarking {
                    HStack {
                        ProgressView()
                        Text("Running…")
                    }
                } else {
                    Label("Run 10× with this question", systemImage: "stopwatch")
                }
            }
            .disabled(store.isBenchmarking || store.isPredicting || (try? draft.question()) == nil)
            .accessibilityIdentifier("layaBenchmarkButton")

            if let report = store.benchmark {
                if let first = report.first {
                    LabeledContent("First run", value: "total \(LayaFormat.seconds(first.total)) · graph \(LayaFormat.seconds(first.graph))")
                        .font(.footnote)
                }
                if let graph = report.stats(\.graph) {
                    statsRow("Graph", graph)
                }
                if let head = report.stats(\.head) {
                    statsRow("Head", head)
                }
                if let pack = report.stats(\.pack) {
                    statsRow("Pack", pack)
                }
                if let host = report.stats(\.hostTensors) {
                    statsRow("Host tensors", host)
                }
                if let total = report.stats(\.total) {
                    statsRow("Total", total)
                }
                copyButton("Copy benchmark", id: "layaCopyBenchmark") { report.text }
            }
        }
    }

    private func statsRow(_ name: String, _ stats: LayaLatencyStats) -> some View {
        LabeledContent(name) {
            VStack(alignment: .trailing, spacing: 1) {
                Text("median \(LayaFormat.seconds(stats.median))").monospacedDigit()
                Text("min \(LayaFormat.seconds(stats.min)) · p95 \(LayaFormat.seconds(stats.p95)) · max \(LayaFormat.seconds(stats.max))")
                    .font(.caption2)
                    .foregroundStyle(.secondary)
                    .monospacedDigit()
            }
        }
    }

    // MARK: Diagnostics

    private var diagnosticsSection: some View {
        Section("Diagnostics") {
            ForEach(Array(store.log.tail(4).enumerated()), id: \.offset) { _, entry in
                Text(entry.line)
                    .font(.caption2.monospaced())
                    .foregroundStyle(.secondary)
                    .lineLimit(2)
            }
            NavigationLink {
                LayaLogView(store: store)
            } label: {
                Label("Full log (\(store.log.entries.count) lines)", systemImage: "doc.text.magnifyingglass")
            }
            .accessibilityIdentifier("layaLogLink")
            copyButton("Copy report", id: "layaCopyReport") { store.report() }
            ShareLink(item: store.report()) {
                Label("Share report", systemImage: "square.and.arrow.up")
            }
            .accessibilityIdentifier("layaShareReport")
        }
    }

    private var deviceSection: some View {
        Section("Device") {
            ForEach(Array(store.device.rows.enumerated()), id: \.offset) { _, row in
                LabeledContent(row.0, value: row.1)
            }
        }
    }

    // MARK: About

    private var aboutSection: some View {
        Section("About") {
            Text(
                "Laya is a typed-decision model: it reads a text and a choice, score, or yes/no question and returns probabilities in one forward pass. No tokens are generated. This is a Swift port of the laya-coreml Python runtime; the encoder runs as a Core ML graph and the token embeddings and action head run on the CPU."
            )
            .font(.footnote)
            .foregroundStyle(.secondary)
            Link("laya-coreml on GitHub", destination: LayaModelSource.sourceURL)
            Link("Model on Hugging Face", destination: LayaModelSource.hubURL)
        }
    }

    // MARK: Actions

    private func ask() async {
        failure = nil
        do {
            let question = try draft.question()
            prediction = try await store.predict(state: draft.state, question: question)
        } catch {
            prediction = nil
            failure = LayaFailure(stage: "predict", error: error)
        }
    }

    /// A button that copies `text()` to the pasteboard and confirms inline.
    private func copyButton(_ title: String, id: String, text: @escaping () -> String) -> some View {
        Button {
            UIPasteboard.general.string = text()
            copied = id
            Task {
                try? await Task.sleep(for: .seconds(2))
                if copied == id { copied = nil }
            }
        } label: {
            Label(copied == id ? "Copied" : title, systemImage: copied == id ? "checkmark" : "doc.on.doc")
        }
        .accessibilityIdentifier(id)
    }

}

/// The whole diagnostics log, selectable, with copy and share.
struct LayaLogView: View {
    @ObservedObject var store: LayaModelStore
    @State private var copied = false

    var body: some View {
        ScrollView {
            Text(store.log.text.isEmpty ? "No log entries yet." : store.log.text)
                .font(.caption.monospaced())
                .textSelection(.enabled)
                .frame(maxWidth: .infinity, alignment: .leading)
                .padding()
                .accessibilityIdentifier("layaLogText")
        }
        .navigationTitle("Laya log")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItemGroup(placement: .topBarTrailing) {
                Button {
                    UIPasteboard.general.string = store.report()
                    copied = true
                    Task {
                        try? await Task.sleep(for: .seconds(2))
                        copied = false
                    }
                } label: {
                    Image(systemName: copied ? "checkmark" : "doc.on.doc")
                }
                .accessibilityIdentifier("layaLogCopy")
                ShareLink(item: store.report()) {
                    Image(systemName: "square.and.arrow.up")
                }
                Button(role: .destructive) {
                    store.clearLog()
                } label: {
                    Image(systemName: "trash")
                }
                .accessibilityIdentifier("layaLogClear")
            }
        }
    }
}

/// The editable form state, and the conversion into a `LayaQuestion`.
struct LayaDraft: Identifiable, Equatable {
    var id: String { title }
    var title: String
    var kind: LayaQuestionKind
    var state: String
    var instructions: String
    /// One option or level per line.
    var options: String

    func question() throws -> LayaQuestion {
        let question: LayaQuestion
        switch kind {
        case .choice:
            question = .choice(instructions: instructions, options: Self.lines(options).map(Self.parseOption))
        case .score:
            question = .score(instructions: instructions, levels: Self.lines(options))
        case .noul:
            question = .noul(instructions: instructions)
        }
        try question.validate()
        return question
    }

    static func lines(_ text: String) -> [String] {
        text.split(whereSeparator: \.isNewline)
            .map { $0.trimmingCharacters(in: .whitespaces) }
            .filter { !$0.isEmpty }
    }

    /// `label: description` or a bare label.
    static func parseOption(_ line: String) -> LayaChoiceOption {
        guard let colon = line.firstIndex(of: ":") else {
            return LayaChoiceOption(line)
        }
        let label = line[..<colon].trimmingCharacters(in: .whitespaces)
        let description = line[line.index(after: colon)...].trimmingCharacters(in: .whitespaces)
        return LayaChoiceOption(label, description.isEmpty ? nil : description)
    }

    static let examples: [LayaDraft] = [
        LayaDraft(
            title: "Support ticket routing",
            kind: .choice,
            state: "Customer: I was charged twice for my order last week and the second charge still shows as pending on my card.",
            instructions: "Which team should handle this message?",
            options: "billing: payments, refunds, and charges\nshipping: delivery and tracking\naccount: login and profile changes\nother"
        ),
        LayaDraft(
            title: "Review sentiment",
            kind: .score,
            state: "The battery lasts two days, the screen is sharp, but the camera struggles the moment the light drops.",
            instructions: "How positive is this product review?",
            options: "very negative\nnegative\nmixed\npositive\nvery positive"
        ),
        LayaDraft(
            title: "Fact check",
            kind: .noul,
            state: "Meeting notes: launch moved from Tuesday to Thursday; design review stays on Monday.",
            instructions: "The launch is on Thursday.",
            options: ""
        ),
    ]
}
