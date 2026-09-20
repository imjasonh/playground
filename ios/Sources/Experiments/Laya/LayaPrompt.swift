import Foundation

/// The slice of a Hugging Face tokenizer the prompt builder needs. Tests use a
/// fake; the app wraps swift-transformers.
protocol LayaTokenizing {
    var maskToken: String { get }
    var clsTokenID: Int { get }
    var sepTokenID: Int { get }
    var padTokenID: Int { get }
    var maskTokenID: Int { get }

    /// Encodes `text` without adding special tokens.
    func encode(_ text: String) -> [Int]
}

/// One prepared question: token ids plus the index of each option's `[MASK]`.
struct LayaPromptItem: Equatable {
    let ids: [Int]
    let markers: [Int]
    let kind: LayaQuestionKind
}

/// Port of `build_prefix` / `build_sequence` from the Python runtime.
///
/// Layout: `[CLS] <type> question: <instructions> [SEP] [MASK] opt0 [MASK] opt1 … [SEP] <state> [SEP]`.
struct LayaPromptBuilder {
    let tokenizer: any LayaTokenizing
    /// Whole-sequence cap (`max_len` in `rl_agent_config.json`).
    var maxLength = 512
    /// Cap on the instructions-plus-options head (`head_max_len`).
    var headMaxLength = 192

    static let optionTokenCap = 48

    /// Builds the question head and the option marker positions.
    func prefix(for question: LayaQuestion) -> (ids: [Int], markers: [Int]) {
        let mask = tokenizer.maskToken
        let options = question.renderedOptions
        let instructions = question.instructions.replacingOccurrences(of: mask, with: " ")
        var headIDs = tokenizer.encode("\(question.kind.name) question: \(instructions)")

        var optionIDs: [[Int]] = options.map { option in
            let text = " " + option.replacingOccurrences(of: mask, with: " ")
            return [tokenizer.maskTokenID] + Array(tokenizer.encode(text).prefix(Self.optionTokenCap))
        }

        var optionBudget = headMaxLength - optionIDs.reduce(0) { $0 + $1.count }
        if optionBudget < 16 {
            let per = max(4, (headMaxLength - 16) / max(1, optionIDs.count))
            optionIDs = optionIDs.map { Array($0.prefix(per)) }
            optionBudget = headMaxLength - optionIDs.reduce(0) { $0 + $1.count }
        }
        headIDs = Array(headIDs.prefix(max(8, optionBudget)))

        var ids = [tokenizer.clsTokenID] + headIDs + [tokenizer.sepTokenID]
        var markers: [Int] = []
        for option in optionIDs {
            markers.append(ids.count)
            ids.append(contentsOf: option)
        }
        ids.append(tokenizer.sepTokenID)
        return (ids, markers)
    }

    /// Appends the state and truncates to `maxLength`.
    func sequence(state: String, question: LayaQuestion) -> (ids: [Int], markers: [Int]) {
        var (ids, markers) = prefix(for: question)
        let room = max(0, maxLength - ids.count - 1)
        let stateText = state.replacingOccurrences(of: tokenizer.maskToken, with: " ")
        let stateIDs = Array(tokenizer.encode(stateText).prefix(room))
        ids += stateIDs
        ids.append(tokenizer.sepTokenID)
        ids = Array(ids.prefix(maxLength))
        markers = markers.filter { $0 < maxLength }
        return (ids, markers)
    }

    /// Validates the question, then builds the item the collator consumes.
    func prepare(state: String, question: LayaQuestion) throws -> LayaPromptItem {
        try question.validate()
        let (ids, markers) = sequence(state: state, question: question)
        guard markers.count == question.optionCount else {
            throw LayaError.optionBudgetExceeded
        }
        return LayaPromptItem(ids: ids, markers: markers, kind: question.kind)
    }
}

/// Fixed input geometry of an export (`shape` in `coreml_config.json`).
struct LayaShape: Equatable, Codable {
    let batchSize: Int
    let maxLength: Int
    let maxOptions: Int

    enum CodingKeys: String, CodingKey {
        case batchSize = "batch_size"
        case maxLength = "max_length"
        case maxOptions = "max_options"
    }

    init(batchSize: Int = 1, maxLength: Int, maxOptions: Int = 32) {
        self.batchSize = batchSize
        self.maxLength = maxLength
        self.maxOptions = maxOptions
    }
}

/// One padded row in the model's input signature (`collate_items`, batch 1).
struct LayaBatch: Equatable {
    /// `input_ids`, padded with the pad id to `length`.
    let inputIDs: [Int]
    /// `attention_mask`; position 0 stays valid even for an empty row.
    let attentionMask: [Bool]
    /// `marker_pos`, zero-padded to `maxOptions`.
    let markerPositions: [Int]
    /// `marker_mask`, one flag per real option.
    let markerMask: [Bool]
    let kind: LayaQuestionKind

    var length: Int { inputIDs.count }
    var maxOptions: Int { markerPositions.count }
    var tokenCount: Int { attentionMask.filter { $0 }.count }
    var optionCount: Int { markerMask.filter { $0 }.count }
}

enum LayaCollator {
    /// Pads `item` into the export's fixed geometry, or throws when it does
    /// not fit. Same messages as the Python `collate_items`.
    static func collate(_ item: LayaPromptItem, shape: LayaShape, padTokenID: Int) throws -> LayaBatch {
        guard item.markers.count <= shape.maxOptions else {
            throw LayaError.tooManyOptions(count: item.markers.count, limit: shape.maxOptions)
        }
        guard item.ids.count <= shape.maxLength else {
            throw LayaError.tooManyTokens(count: item.ids.count, limit: shape.maxLength)
        }
        var inputIDs = Array(repeating: padTokenID, count: shape.maxLength)
        var attention = Array(repeating: false, count: shape.maxLength)
        attention[0] = true
        for (index, id) in item.ids.enumerated() {
            inputIDs[index] = id
            attention[index] = true
        }
        var markerPositions = Array(repeating: 0, count: shape.maxOptions)
        var markerMask = Array(repeating: false, count: shape.maxOptions)
        for (index, position) in item.markers.enumerated() {
            markerPositions[index] = position
            markerMask[index] = true
        }
        return LayaBatch(
            inputIDs: inputIDs,
            attentionMask: attention,
            markerPositions: markerPositions,
            markerMask: markerMask,
            kind: item.kind
        )
    }
}
