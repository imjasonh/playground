import CoreML
import Foundation

/// One answered question plus what it cost.
struct LayaPrediction {
    let decision: LayaDecision
    /// Real tokens in the sequence before padding (`usage.input_tokens`).
    let inputTokens: Int
    let timings: LayaTimings
    /// Output feature names with shapes and element counts, as returned by Core ML.
    let outputSummary: String
}

/// Facts about a loaded model for the status pane and the report.
struct LayaModelInfo: Equatable {
    let revision: String
    let sequenceLength: Int
    let width: Int
    let maxOptions: Int
    let vocabularySize: Int
    let hostWeightsDType: String
    let computeUnits: String
    let signature: LayaSignature
    let modelLoadSeconds: TimeInterval
    let tokenizerLoadSeconds: TimeInterval
    let hostWeightsLoadSeconds: TimeInterval
    let totalLoadSeconds: TimeInterval

    var text: String {
        """
        revision \(revision), \(computeUnits)
        sequence \(sequenceLength) tokens, width \(width), \(maxOptions) option slots, vocab \(vocabularySize), host weights \(hostWeightsDType)
        load: model \(LayaFormat.seconds(modelLoadSeconds)), tokenizer \(LayaFormat.seconds(tokenizerLoadSeconds)), host weights \(LayaFormat.seconds(hostWeightsLoadSeconds)), total \(LayaFormat.seconds(totalLoadSeconds))
        \(signature.text)
        """
    }
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
        let modelLoaded = Date()

        let length = bundle.manifest.shape.maxLength
        let width = bundle.encoderConfig.hiddenSize
        let signature = Self.signature(of: model)
        try Self.checkSignature(signature, width: width, length: length, maxOptions: bundle.manifest.shape.maxOptions)

        let tokenizer = try await LayaHubTokenizer.load(from: bundle.tokenizerURL, specialTokens: bundle.specialTokens)
        let tokenizerLoaded = Date()
        let weights = try LayaHostWeights(file: try LayaSafetensorsFile(url: bundle.hostWeightsURL))
        let weightsLoaded = Date()
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
            maxOptions: bundle.manifest.shape.maxOptions,
            vocabularySize: weights.vocabularySize,
            hostWeightsDType: weights.embedding.dtype.rawValue,
            computeUnits: Self.label(for: computeUnits),
            signature: signature,
            modelLoadSeconds: modelLoaded.timeIntervalSince(start),
            tokenizerLoadSeconds: tokenizerLoaded.timeIntervalSince(modelLoaded),
            hostWeightsLoadSeconds: weightsLoaded.timeIntervalSince(tokenizerLoaded),
            totalLoadSeconds: Date().timeIntervalSince(start)
        )
    }

    // MARK: Signature

    static func signature(of model: MLModel) -> LayaSignature {
        func describe(_ features: [String: MLFeatureDescription]) -> [LayaFeatureDescription] {
            features.keys.sorted().map { name in
                let feature = features[name]
                let constraint = feature?.multiArrayConstraint
                return LayaFeatureDescription(
                    name: name,
                    shape: constraint?.shape.map(\.intValue) ?? [],
                    dataType: constraint.map { label(for: $0.dataType) } ?? label(for: feature?.type)
                )
            }
        }
        return LayaSignature(
            inputs: describe(model.modelDescription.inputDescriptionsByName),
            outputs: describe(model.modelDescription.outputDescriptionsByName)
        )
    }

    /// Same check as the Python agent: five fixed-shape inputs, nothing else.
    static func checkSignature(_ signature: LayaSignature, width: Int, length: Int, maxOptions: Int) throws {
        let expected: [String: [Int]] = [
            "embeddings": [1, width, 1, length],
            "full_mask": [1, length, 1, length],
            "local_mask": [1, length, 1, length],
            "type_vectors": [1, width, 1, 1],
            "marker_map": [1, length, 1, maxOptions],
        ]
        var actual: [String: [Int]] = [:]
        for input in signature.inputs {
            actual[input.name] = input.shape
        }
        guard actual == expected else {
            let expectedText = expected.keys.sorted().map { "\($0): \(expected[$0] ?? [])" }.joined(separator: ", ")
            throw LayaError.model(
                "Package signature mismatch. Expected \(expectedText). Got \(signature.text.replacingOccurrences(of: "\n", with: " "))"
            )
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

    static func label(for type: MLMultiArrayDataType) -> String {
        switch type {
        case .float16: return "float16"
        case .float32: return "float32"
        case .double: return "float64"
        case .int32: return "int32"
        @unknown default: return "dtype \(type.rawValue)"
        }
    }

    static func label(for type: MLFeatureType?) -> String {
        guard let type else { return "missing" }
        switch type {
        case .multiArray: return "multiArray"
        case .double: return "double"
        case .int64: return "int64"
        case .string: return "string"
        case .image: return "image"
        case .dictionary: return "dictionary"
        case .sequence: return "sequence"
        case .state: return "state"
        case .invalid: return "invalid"
        @unknown default: return "type \(type.rawValue)"
        }
    }

    // MARK: Inference

    /// Token count of the prepared sequence, for the budget readout.
    func tokenCount(state: String, question: LayaQuestion) throws -> Int {
        try builder.prepare(state: state, question: question).ids.count
    }

    var maxTokens: Int { shape.maxLength }

    func predict(state: String, question: LayaQuestion) throws -> LayaPrediction {
        var timings = LayaTimings()
        let start = Date()

        let item = try builder.prepare(state: state, question: question)
        let batch = try LayaCollator.collate(item, shape: shape, padTokenID: tokenizer.padTokenID)
        let prepared = Date()
        timings.prepare = prepared.timeIntervalSince(start)

        let inputs = try host.graphInputs(for: batch)
        let hosted = Date()
        timings.hostTensors = hosted.timeIntervalSince(prepared)

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
        let packed = Date()
        timings.pack = packed.timeIntervalSince(hosted)

        let output = try model.prediction(from: provider)
        let predicted = Date()
        timings.graph = predicted.timeIntervalSince(packed)

        // Output names are traced identifiers; element counts tell the two apart
        // (`max_options` slots versus `hidden_size` pooled features).
        var logits: [Float]?
        var pooled: [Float]?
        var summary: [String] = []
        for name in output.featureNames.sorted() {
            guard let array = output.featureValue(for: name)?.multiArrayValue else {
                summary.append("\(name): not a multiArray")
                continue
            }
            let values = Self.floats(from: array)
            summary.append("\(name): \(array.shape.map(\.intValue)) \(Self.label(for: array.dataType)) (\(values.count) values)")
            if values.count == shape.maxOptions {
                logits = values
            } else if values.count == host.weights.width {
                pooled = values
            }
        }
        let outputSummary = summary.joined(separator: "; ")
        guard let logits, let pooled else {
            throw LayaError.model(
                "Graph did not return both \(shape.maxOptions) marker logits and a \(host.weights.width)-wide pooled vector. Outputs: \(outputSummary)"
            )
        }
        let (masked, action) = try host.finish(logits: logits, pooled: pooled, markerMask: batch.markerMask)
        let decision = try LayaResultFormatter.decision(
            logits: masked,
            action: action,
            question: question,
            calibration: calibration
        )
        let finished = Date()
        timings.head = finished.timeIntervalSince(predicted)
        timings.total = finished.timeIntervalSince(start)
        return LayaPrediction(
            decision: decision,
            inputTokens: item.ids.count,
            timings: timings,
            outputSummary: outputSummary
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
            throw LayaError.model("Core ML allocated a non-contiguous input array (strides \(array.strides)).")
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

    // MARK: Compute plan

    /// Asks Core ML where each operation of the compiled program would run
    /// under `computeUnits`. Slow (it re-plans the model), so it is on demand.
    static func computePlan(compiledModelURL: URL, computeUnits: MLComputeUnits) async throws -> LayaComputePlanSummary {
        let start = Date()
        let configuration = MLModelConfiguration()
        configuration.computeUnits = computeUnits
        let plan = try await MLComputePlan.load(contentsOf: compiledModelURL, configuration: configuration)
        guard case .program(let program) = plan.modelStructure else {
            throw LayaError.model("Compute plan is only available for ML Program models; this model is not one.")
        }
        guard let main = program.functions["main"] else {
            throw LayaError.model("Program has no `main` function; functions: \(program.functions.keys.sorted()).")
        }

        var operationCount = 0
        var operationsByDevice: [String: Int] = [:]
        var costByDevice: [String: Double] = [:]
        var offNeuralEngine: [String: Int] = [:]
        var unplanned = 0

        func walk(_ block: MLModelStructure.Program.Block) {
            for operation in block.operations {
                for nested in operation.blocks {
                    walk(nested)
                }
                // `const` operations carry weights, not work; they would swamp the counts.
                guard operation.operatorName != "const" else { continue }
                operationCount += 1
                guard let usage = plan.deviceUsage(for: operation) else {
                    unplanned += 1
                    continue
                }
                let device = label(for: usage.preferred)
                operationsByDevice[device, default: 0] += 1
                if let cost = plan.estimatedCost(of: operation) {
                    costByDevice[device, default: 0] += cost.weight
                }
                if device != LayaComputePlanSummary.neuralEngine {
                    offNeuralEngine[operation.operatorName, default: 0] += 1
                }
            }
        }
        walk(main.block)

        return LayaComputePlanSummary(
            operationCount: operationCount,
            operationsByDevice: operationsByDevice,
            costByDevice: costByDevice,
            offNeuralEngineOperators: offNeuralEngine,
            unplanned: unplanned,
            seconds: Date().timeIntervalSince(start)
        )
    }

    static func label(for device: MLComputeDevice) -> String {
        // `if case` rather than `switch`: the enum's frozenness decides whether
        // `default` or `@unknown default` warns, and warnings fail the build.
        if case .neuralEngine = device { return LayaComputePlanSummary.neuralEngine }
        if case .cpu = device { return LayaComputePlanSummary.cpu }
        if case .gpu = device { return LayaComputePlanSummary.gpu }
        return "Other"
    }
}
