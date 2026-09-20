import XCTest
@testable import Playground

/// Whitespace tokenizer with a vocabulary that grows in first-seen order.
/// Special ids: pad 0, cls 1, sep 2, mask 3; words start at 100.
private final class FakeTokenizer: LayaTokenizing {
    let maskToken = "[MASK]"
    let clsTokenID = 1
    let sepTokenID = 2
    let padTokenID = 0
    let maskTokenID = 3
    private var vocabulary: [String: Int] = [:]

    func encode(_ text: String) -> [Int] {
        text.split(whereSeparator: \.isWhitespace).map { word in
            let key = String(word)
            if let id = vocabulary[key] {
                return id
            }
            let id = 100 + vocabulary.count
            vocabulary[key] = id
            return id
        }
    }
}

final class LayaPromptTests: XCTestCase {
    private let question = LayaQuestion.choice(
        instructions: "pick one",
        options: [LayaChoiceOption("A"), LayaChoiceOption("B", "bee")]
    )

    func testPrefixLayoutAndMarkers() {
        let builder = LayaPromptBuilder(tokenizer: FakeTokenizer())
        let (ids, markers) = builder.prefix(for: question)
        // [CLS] choice question: pick one [SEP] [MASK] A [MASK] B: bee [SEP]
        XCTAssertEqual(ids, [1, 100, 101, 102, 103, 2, 3, 104, 3, 105, 106, 2])
        XCTAssertEqual(markers, [6, 8])
        XCTAssertEqual(markers.map { ids[$0] }, [3, 3])
    }

    func testSequenceAppendsStateAndFinalSeparator() {
        let builder = LayaPromptBuilder(tokenizer: FakeTokenizer())
        let (ids, markers) = builder.sequence(state: "hello world", question: question)
        XCTAssertEqual(ids.count, 15)
        XCTAssertEqual(Array(ids.suffix(3)), [107, 108, 2])
        XCTAssertEqual(markers, [6, 8])
    }

    func testSequenceTruncatesStateToFit() {
        var builder = LayaPromptBuilder(tokenizer: FakeTokenizer())
        builder.maxLength = 14
        let (ids, _) = builder.sequence(state: "hello world again", question: question)
        XCTAssertEqual(ids.count, 14)
        XCTAssertEqual(ids.last, 2)
        XCTAssertEqual(ids[12], 107)
    }

    func testMaskTokenInUserTextIsNeutralized() {
        let builder = LayaPromptBuilder(tokenizer: FakeTokenizer())
        let sneaky = LayaQuestion.choice(
            instructions: "pick [MASK] one",
            options: [LayaChoiceOption("A [MASK]")]
        )
        let (ids, markers) = builder.sequence(state: "[MASK] state", question: sneaky)
        XCTAssertEqual(ids.filter { $0 == 3 }.count, 1)
        XCTAssertEqual(markers.count, 1)
    }

    func testOptionBudgetSqueezesLongOptions() {
        var builder = LayaPromptBuilder(tokenizer: FakeTokenizer())
        builder.headMaxLength = 32
        let long = (0..<10).map { "w\($0)" }.joined(separator: " ")
        let many = LayaQuestion.choice(
            instructions: "pick the best of these many options here please now",
            options: (0..<8).map { LayaChoiceOption("o\($0) \(long)") }
        )
        let (ids, markers) = builder.prefix(for: many)
        XCTAssertEqual(markers.count, 8)
        // Each option shrinks to 4 ids (mask + 3 words); the head keeps its 8-token floor.
        for pair in zip(markers, markers.dropFirst()) {
            XCTAssertEqual(pair.1 - pair.0, 4)
        }
        XCTAssertEqual(markers[0], 1 + 8 + 1)
        XCTAssertEqual(ids.count, 1 + 8 + 1 + 8 * 4 + 1)
    }

    func testPrepareRejectsInvalidQuestion() {
        let builder = LayaPromptBuilder(tokenizer: FakeTokenizer())
        XCTAssertThrowsError(
            try builder.prepare(state: "x", question: .choice(instructions: "pick", options: []))
        ) { error in
            XCTAssertEqual(error as? LayaError, .invalidQuestion("A choice question needs at least one option."))
        }
        XCTAssertThrowsError(
            try builder.prepare(state: "x", question: .score(instructions: "   ", levels: ["a"]))
        )
        XCTAssertThrowsError(
            try builder.prepare(
                state: "x",
                question: .choice(instructions: "pick", options: [LayaChoiceOption("A"), LayaChoiceOption("A")])
            )
        )
    }

    func testNoulRendersDefaultAndCustomSides() {
        XCTAssertEqual(
            LayaQuestion.noul(instructions: "s").renderedOptions,
            ["false: no, the statement does not hold", "true: yes, the statement holds"]
        )
        XCTAssertEqual(
            LayaQuestion.noul(instructions: "s", falseText: "nah", trueText: "yep").renderedOptions,
            ["false: nah", "true: yep"]
        )
        XCTAssertEqual(
            LayaQuestion.score(instructions: "s", levels: ["low", "high"]).renderedOptions,
            ["level 0: low", "level 1: high"]
        )
    }
}

final class LayaCollatorTests: XCTestCase {
    func testCollatePadsToShape() throws {
        let item = LayaPromptItem(ids: [1, 9, 3, 8, 3], markers: [2, 4], kind: .choice)
        let batch = try LayaCollator.collate(item, shape: LayaShape(maxLength: 8, maxOptions: 3), padTokenID: 0)
        XCTAssertEqual(batch.inputIDs, [1, 9, 3, 8, 3, 0, 0, 0])
        XCTAssertEqual(batch.attentionMask, [true, true, true, true, true, false, false, false])
        XCTAssertEqual(batch.markerPositions, [2, 4, 0])
        XCTAssertEqual(batch.markerMask, [true, true, false])
        XCTAssertEqual(batch.tokenCount, 5)
        XCTAssertEqual(batch.optionCount, 2)
        XCTAssertEqual(batch.length, 8)
        XCTAssertEqual(batch.maxOptions, 3)
    }

    func testCollateRejectsOverflow() {
        let tooManyOptions = LayaPromptItem(ids: [1, 2], markers: [0, 1, 1, 1], kind: .choice)
        XCTAssertThrowsError(
            try LayaCollator.collate(tooManyOptions, shape: LayaShape(maxLength: 8, maxOptions: 3), padTokenID: 0)
        ) { error in
            XCTAssertEqual(error as? LayaError, .tooManyOptions(count: 4, limit: 3))
        }
        let tooLong = LayaPromptItem(ids: Array(repeating: 5, count: 9), markers: [1], kind: .score)
        XCTAssertThrowsError(
            try LayaCollator.collate(tooLong, shape: LayaShape(maxLength: 8, maxOptions: 3), padTokenID: 0)
        ) { error in
            XCTAssertEqual(error as? LayaError, .tooManyTokens(count: 9, limit: 8))
        }
    }
}

final class LayaCalibrationTests: XCTestCase {
    func testBuckets() {
        XCTAssertEqual(LayaCalibration.bucket(kind: .choice, optionCount: 2), "choice:2")
        XCTAssertEqual(LayaCalibration.bucket(kind: .choice, optionCount: 4), "choice:3-5")
        XCTAssertEqual(LayaCalibration.bucket(kind: .score, optionCount: 7), "score:6-10")
        XCTAssertEqual(LayaCalibration.bucket(kind: .noul, optionCount: 12), "noul:11+")
    }

    func testScalePrefersBucketOverride() {
        let calibration = LayaCalibration(temperature: [1.5, 2, 3], temperatureByOptions: ["score:2": 0.5])
        XCTAssertEqual(calibration.scale(kind: .choice, optionCount: 4), 1.5)
        XCTAssertEqual(calibration.scale(kind: .score, optionCount: 2), 0.5)
        XCTAssertEqual(calibration.scale(kind: .score, optionCount: 3), 2)
        XCTAssertEqual(calibration.scale(kind: .noul, optionCount: 2), 3)
    }

    func testSoftmaxAndConfidence() {
        let p = LayaMath.softmax([0.0, log(3.0), 0.0])
        XCTAssertEqual(p[0], 0.2, accuracy: 1e-9)
        XCTAssertEqual(p[1], 0.6, accuracy: 1e-9)
        XCTAssertEqual(p.reduce(0, +), 1, accuracy: 1e-12)
        XCTAssertEqual(LayaMath.confidence([1.0 / 3, 1.0 / 3, 1.0 / 3], optionCount: 3), 0, accuracy: 1e-9)
        XCTAssertEqual(LayaMath.confidence([1, 0, 0], optionCount: 3), 1, accuracy: 1e-9)
        XCTAssertEqual(LayaMath.confidence([1], optionCount: 1), 1)
    }

    func testChoiceDecision() throws {
        let question = LayaQuestion.choice(
            instructions: "q",
            options: [LayaChoiceOption("a"), LayaChoiceOption("b"), LayaChoiceOption("c")]
        )
        let decision = try LayaResultFormatter.decision(
            logits: [0, Float(log(3.0)), 0, -1e4],
            action: [0, 0],
            question: question,
            calibration: LayaCalibration()
        )
        XCTAssertEqual(decision.kind, .choice)
        XCTAssertEqual(decision.actProbability, 0.5)
        guard case .choice(let label, let probabilities) = decision.answer else {
            return XCTFail("expected a choice answer")
        }
        XCTAssertEqual(label, "b")
        XCTAssertEqual(probabilities.map(\.label), ["a", "b", "c"])
        XCTAssertEqual(probabilities.map(\.probability), [0.2, 0.6, 0.2])
        XCTAssertEqual(decision.confidence, LayaMath.round4(LayaMath.confidence([0.2, 0.6, 0.2], optionCount: 3)))
    }

    func testTemperatureOverrideAppliesToChoice() throws {
        let question = LayaQuestion.choice(
            instructions: "q",
            options: [LayaChoiceOption("a"), LayaChoiceOption("b"), LayaChoiceOption("c")]
        )
        let decision = try LayaResultFormatter.decision(
            logits: [0, Float(2 * log(3.0)), 0],
            action: [1],
            question: question,
            calibration: LayaCalibration(temperatureByOptions: ["choice:3-5": 2])
        )
        guard case .choice(_, let probabilities) = decision.answer else {
            return XCTFail("expected a choice answer")
        }
        XCTAssertEqual(probabilities.map(\.probability), [0.2, 0.6, 0.2])
        XCTAssertEqual(decision.actProbability, 1)
    }

    func testScoreDecisionIsWeightedMean() throws {
        let question = LayaQuestion.score(instructions: "q", levels: ["low", "mid", "high"])
        let decision = try LayaResultFormatter.decision(
            logits: [1, 1, 1], action: [0, 0], question: question, calibration: LayaCalibration()
        )
        guard case .score(let value, let probabilities, let legend) = decision.answer else {
            return XCTFail("expected a score answer")
        }
        XCTAssertEqual(value, 1)
        XCTAssertEqual(probabilities, [0.3333, 0.3333, 0.3333])
        XCTAssertEqual(legend, ["low", "mid", "high"])
        XCTAssertEqual(decision.confidence, 0)
    }

    func testNoulDecisionUsesTrueSlot() throws {
        let decision = try LayaResultFormatter.decision(
            logits: [0, Float(log(3.0))],
            action: [0, 0],
            question: .noul(instructions: "s"),
            calibration: LayaCalibration()
        )
        XCTAssertEqual(decision.answer, .noul(probability: 0.75))
        XCTAssertEqual(decision.confidence, 0.75)
    }

    func testNonFiniteOutputsThrow() {
        XCTAssertThrowsError(
            try LayaResultFormatter.decision(
                logits: [.nan, 0], action: [0], question: .noul(instructions: "s"), calibration: LayaCalibration()
            )
        )
        XCTAssertThrowsError(
            try LayaResultFormatter.decision(
                logits: [0], action: [0], question: .noul(instructions: "s"), calibration: LayaCalibration()
            )
        )
    }
}

final class LayaHalfTests: XCTestCase {
    func testExactValuesRoundTrip() {
        let smallestNormal = Float(pow(2.0, -14))
        let smallestSubnormal = Float(pow(2.0, -24))
        for value: Float in [0, -0, 1, -1, 0.5, 2, 1024, 65504, -65504, smallestNormal, smallestSubnormal, Float(pow(2.0, -20))] {
            let half = LayaHalf.encode(value)
            XCTAssertEqual(LayaHalf.decode(half), value, "value \(value)")
        }
        XCTAssertEqual(LayaHalf.encode(-0.0), 0x8000)
        XCTAssertEqual(LayaHalf.encode(1), 0x3C00)
        XCTAssertEqual(LayaHalf.encode(-2), 0xC000)
        XCTAssertEqual(LayaHalf.encode(65504), 0x7BFF)
    }

    func testSpecialValues() {
        XCTAssertEqual(LayaHalf.encode(.infinity), 0x7C00)
        XCTAssertEqual(LayaHalf.encode(-.infinity), 0xFC00)
        XCTAssertTrue(LayaHalf.decode(LayaHalf.encode(.nan)).isNaN)
        XCTAssertEqual(LayaHalf.encode(70000), 0x7C00, "overflow saturates to infinity")
        XCTAssertEqual(LayaHalf.encode(1e-9), 0, "underflow flushes to signed zero")
        XCTAssertEqual(LayaHalf.encode(-1e-9), 0x8000)
    }

    func testRoundsToNearestEven() {
        // 1 + 2^-11 sits exactly between 1 and the next half (1 + 2^-10): ties go to even.
        XCTAssertEqual(LayaHalf.encode(1 + Float(pow(2.0, -11))), 0x3C00)
        // 1 + 3 * 2^-11 ties between 0x3C01 and 0x3C02: even wins.
        XCTAssertEqual(LayaHalf.encode(1 + 3 * Float(pow(2.0, -11))), 0x3C02)
        // Just above the tie rounds up.
        XCTAssertEqual(LayaHalf.encode(1 + Float(pow(2.0, -11)) + Float(pow(2.0, -20))), 0x3C01)
        // Mantissa carry: 2047/1024 + almost 1/2048 rounds to 2.0.
        XCTAssertEqual(LayaHalf.encode(1.99999), 0x4000)
    }

    func testBFloat16Decode() {
        XCTAssertEqual(LayaHalf.decodeBFloat16(0x3F80), 1)
        XCTAssertEqual(LayaHalf.decodeBFloat16(0xBF00), -0.5)
        XCTAssertEqual(LayaHalf.decodeBFloat16(0x4049), Float(bitPattern: 0x4049_0000))
    }
}

final class LayaSafetensorsTests: XCTestCase {
    private static func file(header: String, buffer: [UInt8]) -> Data {
        let headerBytes = Array(header.utf8)
        var data = Data()
        var length = UInt64(headerBytes.count).littleEndian
        withUnsafeBytes(of: &length) { data.append(contentsOf: $0) }
        data.append(contentsOf: headerBytes)
        data.append(contentsOf: buffer)
        return data
    }

    private static func le32(_ value: Float) -> [UInt8] {
        withUnsafeBytes(of: value.bitPattern.littleEndian) { Array($0) }
    }

    private static func le16(_ value: UInt16) -> [UInt8] {
        withUnsafeBytes(of: value.littleEndian) { Array($0) }
    }

    func testParsesMixedDTypes() throws {
        var buffer: [UInt8] = []
        for value: Float in [1, 2, 3, 4] { buffer += Self.le32(value) }
        for value: Float in [1.5, -2, 0.25] { buffer += Self.le16(LayaHalf.encode(value)) }
        buffer += Self.le16(0x3F80) + Self.le16(0xBF00)
        let header = """
        {"__metadata__":{"format":"pt"},
         "a":{"dtype":"F32","shape":[2,2],"data_offsets":[0,16]},
         "b":{"dtype":"F16","shape":[3],"data_offsets":[16,22]},
         "c":{"dtype":"BF16","shape":[2],"data_offsets":[22,26]}}
        """
        let file = try LayaSafetensorsFile(data: Self.file(header: header, buffer: buffer))
        XCTAssertEqual(file.tensorNames, ["a", "b", "c"])

        let a = try file.tensor(named: "a")
        XCTAssertEqual(a.dtype, .f32)
        XCTAssertEqual(a.shape, [2, 2])
        XCTAssertEqual(a.floats(), [1, 2, 3, 4])
        XCTAssertEqual(a.row(1), [3, 4])
        XCTAssertEqual(a.floats(from: 1, count: 2), [2, 3])

        XCTAssertEqual(try file.tensor(named: "b").floats(), [1.5, -2, 0.25])
        XCTAssertEqual(try file.tensor(named: "c").floats(), [1, -0.5])
    }

    func testRejectsMalformedFiles() {
        XCTAssertThrowsError(try LayaSafetensorsFile(data: Data([1, 2, 3])))
        XCTAssertThrowsError(try LayaSafetensorsFile(data: Self.file(header: "{}", buffer: []).prefix(9)))

        let badOffsets = Self.file(
            header: #"{"a":{"dtype":"F32","shape":[2],"data_offsets":[0,4]}}"#,
            buffer: [0, 0, 0, 0]
        )
        let file = try? LayaSafetensorsFile(data: badOffsets)
        XCTAssertNotNil(file)
        XCTAssertThrowsError(try file?.tensor(named: "a"))
        XCTAssertThrowsError(try file?.tensor(named: "missing"))

        let unsupported = Self.file(
            header: #"{"a":{"dtype":"I64","shape":[1],"data_offsets":[0,8]}}"#,
            buffer: Array(repeating: 0, count: 8)
        )
        XCTAssertThrowsError(try LayaSafetensorsFile(data: unsupported).tensor(named: "a"))
    }
}

final class LayaANEHostTests: XCTestCase {
    private static let width = 4
    private static let vocabulary = 10

    /// E[id, w] = id * 10 + w, stored as F32.
    private static func embeddingTensor() -> LayaTensor {
        var data = Data()
        for id in 0..<vocabulary {
            for w in 0..<width {
                var bits = Float(id * 10 + w).bitPattern.littleEndian
                withUnsafeBytes(of: &bits) { data.append(contentsOf: $0) }
            }
        }
        return LayaTensor(name: "emb", dtype: .f32, shape: [vocabulary, width], data: data, byteOffset: 0)
    }

    private static func weights() throws -> LayaHostWeights {
        try LayaHostWeights(
            embedding: embeddingTensor(),
            typeEmbedding: [[0, 0, 0, 0], [1, 1, 1, 1], [2, 2, 2, 2]],
            // hidden 2, input width + 4 = 8. Row 0 is all zero; row 1 is all zero with bias 1.
            action0Weight: Array(repeating: 0, count: 2 * 8),
            action0Bias: [0, 1],
            // actions 2: identity over the hidden pair.
            action2Weight: [1, 0, 0, 1],
            action2Bias: [0.5, 0]
        )
    }

    private func host(length: Int = 8, localAttention: Int = 4) throws -> LayaANEHost {
        LayaANEHost(weights: try Self.weights(), length: length, localAttention: localAttention)
    }

    private func batch() throws -> LayaBatch {
        let item = LayaPromptItem(ids: [1, 5, 3, 7, 3, 2], markers: [2, 4], kind: .score)
        return try LayaCollator.collate(item, shape: LayaShape(maxLength: 8, maxOptions: 3), padTokenID: 0)
    }

    func testWeightShapeValidation() {
        XCTAssertThrowsError(
            try LayaHostWeights(
                embedding: Self.embeddingTensor(),
                typeEmbedding: [[0, 0, 0, 0]],
                action0Weight: Array(repeating: 0, count: 16),
                action0Bias: [0, 1],
                action2Weight: [1, 0, 0, 1],
                action2Bias: [0, 0]
            )
        )
        XCTAssertThrowsError(
            try LayaHostWeights(
                embedding: Self.embeddingTensor(),
                typeEmbedding: [[0, 0, 0, 0], [1, 1, 1, 1], [2, 2, 2, 2]],
                action0Weight: Array(repeating: 0, count: 15),
                action0Bias: [0, 1],
                action2Weight: [1, 0, 0, 1],
                action2Bias: [0, 0]
            )
        )
    }

    func testEmbeddingsAreWidthMajor() throws {
        let inputs = try host().graphInputs(for: batch())
        XCTAssertEqual(inputs.width, 4)
        XCTAssertEqual(inputs.length, 8)
        XCTAssertEqual(inputs.maxOptions, 3)
        XCTAssertEqual(inputs.embeddings.count, 4 * 8)
        // embeddings[w * length + position] = E[id, w]
        XCTAssertEqual(inputs.embeddings[0 * 8 + 1], 50) // id 5, w 0
        XCTAssertEqual(inputs.embeddings[3 * 8 + 1], 53) // id 5, w 3
        XCTAssertEqual(inputs.embeddings[2 * 8 + 3], 72) // id 7, w 2
        XCTAssertEqual(inputs.embeddings[1 * 8 + 7], 1) // pad id 0, w 1
        XCTAssertEqual(inputs.typeVector, [1, 1, 1, 1])
    }

    func testMasksFollowKeyValidityAndLocalWindow() throws {
        let inputs = try host().graphInputs(for: batch())
        let length = 8
        func full(_ key: Int, _ query: Int) -> Float { inputs.fullMask[key * length + query] }
        func local(_ key: Int, _ query: Int) -> Float { inputs.localMask[key * length + query] }

        // Keys 0..<6 are real tokens; keys 6 and 7 are padding.
        for query in 0..<length {
            for key in 0..<6 { XCTAssertEqual(full(key, query), 0) }
            for key in 6..<8 { XCTAssertEqual(full(key, query), -1e4) }
        }
        // Window is localAttention / 2 = 2 around the query.
        XCTAssertEqual(local(0, 0), 0)
        XCTAssertEqual(local(2, 0), 0)
        XCTAssertEqual(local(3, 0), -1e4)
        XCTAssertEqual(local(5, 3), 0)
        XCTAssertEqual(local(5, 2), -1e4)
        // Padding queries may see every valid key so their rows stay finite.
        XCTAssertEqual(local(0, 7), 0)
        XCTAssertEqual(local(5, 7), 0)
        // Padding keys stay masked even for nearby queries.
        XCTAssertEqual(local(6, 7), -1e4)
    }

    func testMarkerMapPlacesOneHotPerSlot() throws {
        let inputs = try host().graphInputs(for: batch())
        XCTAssertEqual(inputs.markerMap.count, 8 * 3)
        XCTAssertEqual(inputs.markerMap.filter { $0 == 1 }.count, 3)
        XCTAssertEqual(inputs.markerMap[2 * 3 + 0], 1)
        XCTAssertEqual(inputs.markerMap[4 * 3 + 1], 1)
        // The unused slot points at position 0, as the Python zero-padding does.
        XCTAssertEqual(inputs.markerMap[0 * 3 + 2], 1)
    }

    func testGraphInputsRejectBadBatches() throws {
        XCTAssertThrowsError(try host(length: 16).graphInputs(for: batch()))
        let outOfVocabulary = LayaBatch(
            inputIDs: [1, 42, 0, 0, 0, 0, 0, 0],
            attentionMask: [true, true, false, false, false, false, false, false],
            markerPositions: [1, 0, 0],
            markerMask: [true, false, false],
            kind: .choice
        )
        XCTAssertThrowsError(try host().graphInputs(for: outOfVocabulary)) { error in
            XCTAssertEqual(error as? LayaError, .model("Token id 42 outside checkpoint vocabulary"))
        }
    }

    func testFinishMasksUnusedSlotsAndRunsActionHead() throws {
        let (logits, action) = try host().finish(
            logits: [1, 2, 3],
            pooled: [0.1, 0.2, 0.3, 0.4],
            markerMask: [true, true, false]
        )
        XCTAssertEqual(logits, [1, 2, -1e4])
        XCTAssertEqual(action.count, 2)
        XCTAssertEqual(action[0], 0.5, accuracy: 1e-6)
        XCTAssertEqual(action[1], LayaANEHost.geluErf(1), accuracy: 1e-6)
        XCTAssertEqual(LayaANEHost.geluErf(1), 0.8413447, accuracy: 1e-6)
        XCTAssertEqual(LayaANEHost.geluErf(0), 0)
    }

    func testFinishRejectsShapeMismatch() throws {
        XCTAssertThrowsError(try host().finish(logits: [1, 2], pooled: [0, 0, 0, 0], markerMask: [true, true, false]))
        XCTAssertThrowsError(try host().finish(logits: [1, 2, 3], pooled: [0, 0], markerMask: [true, true, false]))
    }
}

final class LayaBundleTests: XCTestCase {
    func testManifestValidation() throws {
        let good = """
        {"format":"laya-coreml-ane","format_version":1,
         "shape":{"batch_size":1,"max_length":512,"max_options":32},
         "files":{"host_weights.safetensors":{"sha256":"abc"},"tokenizer/tokenizer.json":{}}}
        """
        let manifest = try JSONDecoder().decode(LayaManifest.self, from: Data(good.utf8))
        XCTAssertNoThrow(try manifest.validateANE())
        XCTAssertEqual(manifest.layaShape, LayaShape(batchSize: 1, maxLength: 512, maxOptions: 32))
        XCTAssertEqual(manifest.files?["host_weights.safetensors"]?.sha256, "abc")
        XCTAssertNil(manifest.files?["tokenizer/tokenizer.json"]?.sha256)

        let flexible = """
        {"format":"laya-coreml-ane","format_version":1,
         "shape":{"batch_size":1,"max_length":512,"max_options":32,"flexible":true}}
        """
        XCTAssertThrowsError(try JSONDecoder().decode(LayaManifest.self, from: Data(flexible.utf8)).validateANE())

        let cpu = """
        {"format":"laya-coreml","format_version":1,
         "shape":{"batch_size":1,"max_length":512,"max_options":32}}
        """
        XCTAssertThrowsError(try JSONDecoder().decode(LayaManifest.self, from: Data(cpu.utf8)).validateANE())
    }

    func testAgentConfigDefaults() throws {
        let config = try JSONDecoder().decode(LayaAgentConfig.self, from: Data("{}".utf8))
        XCTAssertEqual(config.maxLength, 512)
        XCTAssertEqual(config.headMaxLength, 192)
        XCTAssertEqual(config.calibration, LayaCalibration())

        let tuned = try JSONDecoder().decode(
            LayaAgentConfig.self,
            from: Data(#"{"max_len":256,"temperature":[1.2,0.9,1.1],"temperature_by_options":{"choice:2":0.8}}"#.utf8)
        )
        XCTAssertEqual(tuned.maxLength, 256)
        XCTAssertEqual(tuned.calibration.scale(kind: .choice, optionCount: 2), 0.8)
        XCTAssertEqual(tuned.calibration.scale(kind: .score, optionCount: 4), 0.9)
    }

    func testEncoderConfig() throws {
        let config = try JSONDecoder().decode(LayaEncoderConfig.self, from: Data(#"{"hidden_size":768}"#.utf8))
        XCTAssertEqual(config.hiddenSize, 768)
        XCTAssertEqual(config.localAttention, 128)
    }

    func testSpecialTokensAcceptStringsAndAddedTokenObjects() throws {
        let config = """
        {"cls_token":"[CLS]","sep_token":{"content":"[SEP]","lstrip":false},
         "pad_token":"[PAD]","mask_token":{"content":"[MASK]"}}
        """
        let tokens = try LayaSpecialTokens(tokenizerConfig: Data(config.utf8))
        XCTAssertEqual(tokens, LayaSpecialTokens(cls: "[CLS]", sep: "[SEP]", pad: "[PAD]", mask: "[MASK]"))

        XCTAssertThrowsError(
            try LayaSpecialTokens(tokenizerConfig: Data(#"{"cls_token":"[CLS]","sep_token":"[SEP]","pad_token":"[PAD]"}"#.utf8))
        ) { error in
            XCTAssertEqual(error as? LayaError, .bundle("Tokenizer is missing a valid mask_token"))
        }
    }

    func testSHA256OfFile() throws {
        let url = FileManager.default.temporaryDirectory.appendingPathComponent("laya-sha-\(UUID().uuidString)")
        try Data("abc".utf8).write(to: url)
        defer { try? FileManager.default.removeItem(at: url) }
        XCTAssertEqual(
            try LayaBundle.sha256Hex(of: url),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        )
    }
}

final class LayaDraftTests: XCTestCase {
    func testParsesOptionsWithAndWithoutDescriptions() {
        XCTAssertEqual(LayaDraft.parseOption("billing: payments and refunds"), LayaChoiceOption("billing", "payments and refunds"))
        XCTAssertEqual(LayaDraft.parseOption("other"), LayaChoiceOption("other"))
        XCTAssertEqual(LayaDraft.parseOption("empty:"), LayaChoiceOption("empty"))
        XCTAssertEqual(LayaDraft.lines(" a \n\n b\nc "), ["a", "b", "c"])
    }

    func testExamplesProduceValidQuestions() throws {
        for example in LayaDraft.examples {
            let question = try example.question()
            XCTAssertEqual(question.kind, example.kind, example.title)
        }
        XCTAssertEqual(Set(LayaDraft.examples.map(\.id)).count, LayaDraft.examples.count)
    }

    func testEmptyOptionsAreRejected() {
        let draft = LayaDraft(title: "t", kind: .choice, state: "s", instructions: "pick", options: "\n")
        XCTAssertThrowsError(try draft.question())
        let score = LayaDraft(title: "t", kind: .score, state: "s", instructions: "", options: "a\nb")
        XCTAssertThrowsError(try score.question())
    }
}
