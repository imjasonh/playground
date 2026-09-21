import Foundation

/// The six host tensors an ANE bundle keeps outside the Core ML graph.
struct LayaHostWeights {
    /// `encoder.embeddings.tok_embeddings.weight`, `[vocab, width]`; rows convert on demand.
    let embedding: LayaTensor
    /// `type_emb.weight`, `[3, width]`.
    let typeEmbedding: [[Float]]
    /// `act_head.0.weight`, `[hidden, width + 4]` (row-major).
    let action0Weight: [Float]
    let action0Bias: [Float]
    /// `act_head.2.weight`, `[actions, hidden]`.
    let action2Weight: [Float]
    let action2Bias: [Float]

    var vocabularySize: Int { embedding.shape[0] }
    var width: Int { embedding.shape[1] }
    var hiddenSize: Int { action0Bias.count }
    var actionCount: Int { action2Bias.count }

    init(
        embedding: LayaTensor,
        typeEmbedding: [[Float]],
        action0Weight: [Float],
        action0Bias: [Float],
        action2Weight: [Float],
        action2Bias: [Float]
    ) throws {
        guard embedding.shape.count == 2 else {
            throw LayaError.bundle("Embedding table must be 2-D, got \(embedding.shape).")
        }
        let width = embedding.shape[1]
        guard typeEmbedding.count == 3, typeEmbedding.allSatisfy({ $0.count == width }) else {
            throw LayaError.bundle("type_emb.weight must be [3, \(width)].")
        }
        let hidden = action0Bias.count
        guard hidden > 0, action0Weight.count == hidden * (width + 4) else {
            throw LayaError.bundle("act_head.0.weight must be [hidden, \(width + 4)].")
        }
        guard !action2Bias.isEmpty, action2Weight.count == action2Bias.count * hidden else {
            throw LayaError.bundle("act_head.2.weight must be [actions, \(hidden)].")
        }
        self.embedding = embedding
        self.typeEmbedding = typeEmbedding
        self.action0Weight = action0Weight
        self.action0Bias = action0Bias
        self.action2Weight = action2Weight
        self.action2Bias = action2Bias
    }

    init(file: LayaSafetensorsFile) throws {
        let typeTensor = try file.tensor(named: "type_emb.weight")
        guard typeTensor.shape.count == 2 else {
            throw LayaError.bundle("type_emb.weight must be 2-D.")
        }
        let w0 = try file.tensor(named: "act_head.0.weight")
        let w2 = try file.tensor(named: "act_head.2.weight")
        guard w0.shape.count == 2, w2.shape.count == 2 else {
            throw LayaError.bundle("Action head weights must be 2-D.")
        }
        try self.init(
            embedding: try file.tensor(named: "encoder.embeddings.tok_embeddings.weight"),
            typeEmbedding: (0..<typeTensor.shape[0]).map { typeTensor.row($0) },
            action0Weight: w0.floats(),
            action0Bias: try file.tensor(named: "act_head.0.bias").floats(),
            action2Weight: w2.floats(),
            action2Bias: try file.tensor(named: "act_head.2.bias").floats()
        )
    }
}

/// The five graph inputs, flattened row-major in the shapes the export declares.
struct LayaGraphInputs: Equatable {
    /// `[1, width, 1, length]`
    let embeddings: [Float]
    /// `[1, length(key), 1, length(query)]`, `0` where attendable, `-1e4` where not.
    let fullMask: [Float]
    let localMask: [Float]
    /// `[1, width, 1, 1]`
    let typeVector: [Float]
    /// `[1, length, 1, maxOptions]`
    let markerMap: [Float]
    let width: Int
    let length: Int
    let maxOptions: Int
}

/// Ports `ANEAgent.model_inputs` and the CPU tail of `ANEAgent.forward`.
struct LayaANEHost {
    let weights: LayaHostWeights
    let length: Int
    /// `local_attention` from `encoder/config.json`; the window is half of it.
    let localAttention: Int

    static let maskedScore: Float = -1e4

    var window: Int { localAttention / 2 }

    /// Builds the graph inputs for one collated row.
    func graphInputs(for batch: LayaBatch) throws -> LayaGraphInputs {
        guard batch.length == length else {
            throw LayaError.model("Batch length \(batch.length) does not match the export length \(length).")
        }
        guard batch.attentionMask.contains(true) else {
            throw LayaError.model("Every batch row needs at least one valid attention key")
        }
        for id in batch.inputIDs where id < 0 || id >= weights.vocabularySize {
            throw LayaError.model("Token id \(id) outside checkpoint vocabulary")
        }
        for position in batch.markerPositions where position < 0 || position >= length {
            throw LayaError.model("Marker position \(position) outside exported sequence")
        }

        let width = weights.width
        // embeddings[0, w, 0, l] = E[ids[l], w]
        var embeddings = [Float](repeating: 0, count: width * length)
        for (position, id) in batch.inputIDs.enumerated() {
            let row = weights.embedding.row(id)
            for w in 0..<width {
                embeddings[w * length + position] = row[w]
            }
        }

        // Python builds [query, key] then transposes to [key, 1, query].
        let valid = batch.attentionMask
        var fullMask = [Float](repeating: Self.maskedScore, count: length * length)
        var localMask = [Float](repeating: Self.maskedScore, count: length * length)
        for query in 0..<length {
            for key in 0..<length where valid[key] {
                let index = key * length + query
                fullMask[index] = 0
                if abs(query - key) <= window || !valid[query] {
                    localMask[index] = 0
                }
            }
        }

        var markerMap = [Float](repeating: 0, count: length * batch.maxOptions)
        for (slot, position) in batch.markerPositions.enumerated() {
            markerMap[position * batch.maxOptions + slot] = 1
        }

        return LayaGraphInputs(
            embeddings: embeddings,
            fullMask: fullMask,
            localMask: localMask,
            typeVector: weights.typeEmbedding[batch.kind.rawValue],
            markerMap: markerMap,
            width: width,
            length: length,
            maxOptions: batch.maxOptions
        )
    }

    /// Masks unused option slots, then runs the two-layer action head.
    ///
    /// - Returns: The masked marker logits and the raw action logits.
    func finish(logits rawLogits: [Float], pooled: [Float], markerMask: [Bool]) throws -> (logits: [Float], action: [Float]) {
        guard rawLogits.count == markerMask.count else {
            throw LayaError.model("Graph returned \(rawLogits.count) logits for \(markerMask.count) option slots.")
        }
        guard pooled.count == weights.width else {
            throw LayaError.model("Graph returned a pooled vector of \(pooled.count), expected \(weights.width).")
        }
        let logits = zip(rawLogits, markerMask).map { $1 ? $0 : Self.maskedScore }
        let p = LayaMath.softmax(logits.map(Double.init))
        let k = Double(max(markerMask.filter { $0 }.count, 2))
        let entropy = -p.reduce(0) { $0 + $1 * log(max($1, 1e-9)) } / log(k)
        let sorted = p.sorted()
        let top = sorted[sorted.count - 1]
        let second = sorted[sorted.count - 2]
        let features = [Float(top), Float(top - second), Float(entropy), Float(k / 255)]

        let input = pooled + features
        let hidden = weights.hiddenSize
        let inputSize = input.count
        var activations = [Float](repeating: 0, count: hidden)
        for h in 0..<hidden {
            var sum = weights.action0Bias[h]
            let rowStart = h * inputSize
            for i in 0..<inputSize {
                sum += input[i] * weights.action0Weight[rowStart + i]
            }
            activations[h] = Self.geluErf(sum)
        }
        var action = [Float](repeating: 0, count: weights.actionCount)
        for a in 0..<weights.actionCount {
            var sum = weights.action2Bias[a]
            let rowStart = a * hidden
            for h in 0..<hidden {
                sum += activations[h] * weights.action2Weight[rowStart + h]
            }
            action[a] = sum
        }
        return (logits, action)
    }

    /// Exact erf GELU, matching the Python host (no tanh approximation).
    static func geluErf(_ x: Float) -> Float {
        let xd = Double(x)
        return Float(xd * (1 + erf(xd / 2.0.squareRoot())) / 2)
    }
}
