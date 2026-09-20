import SwiftUI

/// Download the Laya ANE bundle, then ask it typed questions about a text.
struct LayaView: View {
    @StateObject private var store = LayaModelStore()
    @State private var draft = LayaDraft.examples[0]
    @State private var prediction: LayaPrediction?
    @State private var errorMessage: String?

    var body: some View {
        Form {
            modelSection
            if store.phase == .ready {
                questionSection
                resultSection
            }
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
            switch store.phase {
            case .notDownloaded, .failed:
                Button {
                    Task { await store.prepare() }
                } label: {
                    Label(
                        store.isDownloaded ? "Load model" : "Download model (\(Self.sizeText))",
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
                    LabeledContent("Sequence", value: "\(info.sequenceLength) tokens")
                    LabeledContent("Compute", value: info.computeUnits)
                    LabeledContent("Load time", value: Self.seconds(info.loadSeconds))
                }
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
        case .failed(let message): return message
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
                        errorMessage = nil
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
                if store.isPredicting {
                    ProgressView()
                } else {
                    Label("Ask", systemImage: "sparkles")
                }
            }
            .disabled(store.isPredicting)
            .accessibilityIdentifier("layaAskButton")

            if let errorMessage {
                Text(errorMessage)
                    .font(.footnote)
                    .foregroundStyle(.orange)
                    .accessibilityIdentifier("layaError")
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
                answerRows(prediction.decision)
                LabeledContent("Confidence", value: Self.percent(prediction.decision.confidence))
                LabeledContent("Act probability", value: Self.percent(prediction.decision.actProbability))
                LabeledContent("Input tokens", value: "\(prediction.inputTokens)")
                LabeledContent("Latency", value: Self.seconds(prediction.latency))
            }
            .accessibilityIdentifier("layaResult")
        }
    }

    @ViewBuilder
    private func answerRows(_ decision: LayaDecision) -> some View {
        switch decision.answer {
        case .choice(let label, let probabilities):
            LabeledContent("Choice", value: label)
                .font(.headline)
                .accessibilityIdentifier("layaAnswer")
            ForEach(Array(probabilities.enumerated()), id: \.offset) { _, item in
                probabilityBar(item.label, item.probability)
            }
        case .score(let value, let probabilities, let legend):
            LabeledContent("Score", value: String(format: "%.2f", value))
                .font(.headline)
                .accessibilityIdentifier("layaAnswer")
            ForEach(Array(probabilities.enumerated()), id: \.offset) { index, probability in
                probabilityBar(index < legend.count ? legend[index] : "level \(index)", probability)
            }
        case .noul(let probability):
            LabeledContent("Holds", value: probability >= 0.5 ? "Yes" : "No")
                .font(.headline)
                .accessibilityIdentifier("layaAnswer")
            probabilityBar("true", probability)
            probabilityBar("false", 1 - probability)
        }
    }

    private func probabilityBar(_ label: String, _ probability: Double) -> some View {
        VStack(alignment: .leading, spacing: 2) {
            HStack {
                Text(label).lineLimit(1)
                Spacer()
                Text(Self.percent(probability)).monospacedDigit().foregroundStyle(.secondary)
            }
            .font(.subheadline)
            ProgressView(value: min(max(probability, 0), 1))
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
        errorMessage = nil
        do {
            let question = try draft.question()
            prediction = try await store.predict(state: draft.state, question: question)
        } catch {
            prediction = nil
            errorMessage = (error as? LayaError)?.errorDescription ?? error.localizedDescription
        }
    }

    // MARK: Formatting

    private static var sizeText: String {
        ByteCountFormatter.string(fromByteCount: LayaModelSource.approximateBytes, countStyle: .file)
    }

    private static func percent(_ value: Double) -> String {
        String(format: "%.1f%%", value * 100)
    }

    private static func seconds(_ value: TimeInterval) -> String {
        value < 1 ? String(format: "%.0f ms", value * 1000) : String(format: "%.2f s", value)
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
