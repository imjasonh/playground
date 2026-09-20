import CoreML
import Foundation

/// One answered question plus what it cost.
struct LayaPrediction {
    let decision: LayaDecision
    /// Real tokens in the sequence before padding (`usage.input_tokens`).
    let inputTokens: Int
    /// Wall time for host tensors, the Core ML graph, and the action head.
    let latency: TimeInterval
}

/// Facts about a loaded model for the status pane.
struct LayaModelInfo: Equatable {
    let revision: String
    let sequenceLength: Int
    let width: Int
    let vocabularySize: Int
    let computeUnits: String
    let loadSeconds: TimeInterval
}

/// A loaded ANE bundle: tokenizer, host tensors, and the compiled Core ML graph.
///
/// `MLModel` is not `Sendable`. The runtime is built once off the main actor and
/// after that only `predict` touches the model, one call at a time from the
/// store's serial task, so sharing the reference is safe.
final class LayaRuntime: @unchecked Sendable {
    private let model: MLModel
    private let tokenizer: LayaHubTokenizer
    private let host: LayaANEHost
    private let builder: LayaPromptBuilder
    private let calibration: LayaCalibration
    private let shape: LayaShape
    let info: LayaModelInfo

    static let inputNames = ["embeddings", "full_mask", "local_mask", "type_vectors", "marker_map"]

    init(bundle: LayaBundle, compiledModelURL: URL, revision: String, computeUnits: MLComputeUnits) async throws {
        let start = Date()
        let configuration = MLModelConfiguration()
        configuration.computeUnits = computeUnits
        let model = try await MLModel.load(contentsOf: compiledModelURL, configuration: configuration)

        let length = bundle.manifest.shape.maxLength
        let width = bundle.encoderConfig.hiddenSize
        try Self.checkSignature(of: model, width: width, length: length, maxOptions: bundle.manifest.shape.maxOptions)

        let tokenizer = try await LayaHubTokenizer.load(from: bundle.tokenizerURL, specialTokens: bundle.specialTokens)
        let weights = try LayaHostWeights(file: try LayaSafetensorsFile(url: bundle.hostWeightsURL))
        guard weights.width == width else {
            throw LayaError.bundle("Embedding width \(weights.width) does not match hidden_size \(width).")
        }

        self.model = model
        self.tokenizer = tokenizer
        self.host = LayaANEHost(weights: weights, length: length, localAttention: bundle.encoderConfig.localAttention)
        // The Python runtime truncates the state to `max_len` and then rejects
        // sequences longer than the export. Capping at the export length here
        // means a long state is trimmed instead of refused; the prefix is
        // unchanged, so accepted inputs tokenize identically.
        self.builder = LayaPromptBuilder(
            tokenizer: tokenizer,
            maxLength: min(bundle.agentConfig.maxLength, length),
            headMaxLength: bundle.agentConfig.headMaxLength
        )
        self.calibration = bundle.agentConfig.calibration
        self.shape = bundle.manifest.layaShape
        self.info = LayaModelInfo(
            revision: revision,
            sequenceLength: length,
            width: width,
            vocabularySize: weights.vocabularySize,
            computeUnits: Self.label(for: computeUnits),
            loadSeconds: Date().timeIntervalSince(start)
        )
    }

    /// Same check as the Python agent: five fixed-shape inputs, nothing else.
    private static func checkSignature(of model: MLModel, width: Int, length: Int, maxOptions: Int) throws {
        let expected: [String: [Int]] = [
            "embeddings": [1, width, 1, length],
            "full_mask": [1, length, 1, length],
            "local_mask": [1, length, 1, length],
            "type_vectors": [1, width, 1, 1],
            "marker_map": [1, length, 1, maxOptions],
        ]
        let inputs = model.modelDescription.inputDescriptionsByName
        var actual: [String: [Int]] = [:]
        for (name, description) in inputs {
            actual[name] = description.multiArrayConstraint?.shape.map(\.intValue) ?? []
        }
        guard actual == expected else {
            throw LayaError.model("Package signature mismatch: expected \(expected), got \(actual)")
        }
    }

    static func label(for units: MLComputeUnits) -> String {
        switch units {
        case .cpuOnly: return "CPU only"
        case .cpuAndGPU: return "CPU + GPU"
        case .cpuAndNeuralEngine: return "CPU + Neural Engine"
        case .all: return "All compute units"
        @unknown default: return "Unknown"
        }
    }

    /// Token count of the prepared sequence, for the budget readout.
    func tokenCount(state: String, question: LayaQuestion) throws -> Int {
        try builder.prepare(state: state, question: question).ids.count
    }

    var maxTokens: Int { shape.maxLength }

    func predict(state: String, question: LayaQuestion) throws -> LayaPrediction {
        let item = try builder.prepare(state: state, question: question)
        let batch = try LayaCollator.collate(item, shape: shape, padTokenID: tokenizer.padTokenID)

        let start = Date()
        let inputs = try host.graphInputs(for: batch)
        let embeddings = try Self.halfArray(inputs.embeddings, shape: [1, inputs.width, 1, inputs.length])
        let fullMask = try Self.halfArray(inputs.fullMask, shape: [1, inputs.length, 1, inputs.length])
        let localMask = try Self.halfArray(inputs.localMask, shape: [1, inputs.length, 1, inputs.length])
        let typeVectors = try Self.halfArray(inputs.typeVector, shape: [1, inputs.width, 1, 1])
        let markerMap = try Self.halfArray(inputs.markerMap, shape: [1, inputs.length, 1, inputs.maxOptions])
        let provider = try MLDictionaryFeatureProvider(dictionary: [
            "embeddings": MLFeatureValue(multiArray: embeddings),
            "full_mask": MLFeatureValue(multiArray: fullMask),
            "local_mask": MLFeatureValue(multiArray: localMask),
            "type_vectors": MLFeatureValue(multiArray: typeVectors),
            "marker_map": MLFeatureValue(multiArray: markerMap),
        ])
        let output = try model.prediction(from: provider)

        // Output names are traced identifiers; element counts tell the two apart
        // (`max_options` slots versus `hidden_size` pooled features).
        var logits: [Float]?
        var pooled: [Float]?
        for name in output.featureNames {
            guard let array = output.featureValue(for: name)?.multiArrayValue else { continue }
            let values = Self.floats(from: array)
            if values.count == shape.maxOptions {
                logits = values
            } else if values.count == host.weights.width {
                pooled = values
            }
        }
        guard let logits, let pooled else {
            throw LayaError.model("Graph did not return both marker logits and a pooled vector.")
        }
        let (masked, action) = try host.finish(logits: logits, pooled: pooled, markerMask: batch.markerMask)
        let decision = try LayaResultFormatter.decision(
            logits: masked,
            action: action,
            question: question,
            calibration: calibration
        )
        return LayaPrediction(
            decision: decision,
            inputTokens: item.ids.count,
            latency: Date().timeIntervalSince(start)
        )
    }

    /// Packs `values` into a float16 `MLMultiArray` of `shape`.
    static func halfArray(_ values: [Float], shape: [Int]) throws -> MLMultiArray {
        let array = try MLMultiArray(shape: shape.map { NSNumber(value: $0) }, dataType: .float16)
        guard array.count == values.count else {
            throw LayaError.model("Tensor has \(values.count) values for shape \(shape).")
        }
        var expectedStride = 1
        var contiguous = true
        for (dimension, stride) in zip(shape.reversed(), array.strides.reversed()) {
            if stride.intValue != expectedStride {
                contiguous = false
            }
            expectedStride *= dimension
        }
        guard contiguous else {
            throw LayaError.model("Core ML allocated a non-contiguous input array.")
        }
        array.withUnsafeMutableBytes { raw, _ in
            let halves = raw.bindMemory(to: UInt16.self)
            for index in values.indices {
                halves[index] = LayaHalf.encode(values[index])
            }
        }
        return array
    }

    static func floats(from array: MLMultiArray) -> [Float] {
        (0..<array.count).map { array[$0].floatValue }
    }
}
