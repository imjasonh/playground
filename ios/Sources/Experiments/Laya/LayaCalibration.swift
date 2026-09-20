import Foundation

/// Temperature calibration from `rl_agent_config.json`.
struct LayaCalibration: Equatable {
    /// One temperature per question kind, indexed by `LayaQuestionKind.rawValue`.
    var temperature: [Double] = [1, 1, 1]
    /// Overrides keyed by `"<kind>:<bucket>"`, for example `"choice:3-5"`.
    var temperatureByOptions: [String: Double] = [:]

    /// `temp_bucket` in the Python runtime.
    static func bucket(kind: LayaQuestionKind, optionCount k: Int) -> String {
        let size: String
        if k <= 2 {
            size = "2"
        } else if k <= 5 {
            size = "3-5"
        } else if k <= 10 {
            size = "6-10"
        } else {
            size = "11+"
        }
        return "\(kind.name):\(size)"
    }

    func scale(kind: LayaQuestionKind, optionCount: Int) -> Double {
        if let override = temperatureByOptions[Self.bucket(kind: kind, optionCount: optionCount)] {
            return override
        }
        let index = kind.rawValue
        return index < temperature.count ? temperature[index] : 1
    }
}

enum LayaMath {
    static func softmax(_ values: [Double]) -> [Double] {
        guard let maxValue = values.max() else { return [] }
        let exps = values.map { exp($0 - maxValue) }
        let total = exps.reduce(0, +)
        return exps.map { $0 / total }
    }

    static func softmax(_ values: [Float]) -> [Float] {
        softmax(values.map(Double.init)).map(Float.init)
    }

    /// `confidence_from_probs`: `1 - H(p) / log(k)`, clipped to `[0, 1]`.
    static func confidence(_ probabilities: [Double], optionCount k: Int) -> Double {
        guard k >= 2 else { return 1 }
        let p = probabilities.prefix(k)
        let entropy = -p.reduce(0) { $0 + $1 * log(min(max($1, 1e-12), 1)) }
        return min(max(1 - entropy / log(Double(k)), 0), 1)
    }

    static func round4(_ value: Double) -> Double {
        (value * 10_000).rounded() / 10_000
    }
}

struct LayaLabeledProbability: Equatable {
    let label: String
    let probability: Double
}

/// The typed part of one answer.
enum LayaAnswer: Equatable {
    /// `choice` and the probability of each label, in option order.
    case choice(label: String, probabilities: [LayaLabeledProbability])
    /// `score` is the probability-weighted mean level index.
    case score(value: Double, probabilities: [Double], legend: [String])
    /// `noul` is the probability that the statement holds.
    case noul(probability: Double)
}

/// One decision, in the shape of the Python `answers[qid]` dictionary.
struct LayaDecision: Equatable {
    let kind: LayaQuestionKind
    let answer: LayaAnswer
    /// Normalized-entropy confidence (for `noul`, `max(p, 1 - p)`).
    let confidence: Double
    /// Probability from the small action head (`act_probability`).
    let actProbability: Double
}

enum LayaResultFormatter {
    /// Ports the per-row loop of `ResultMixin.system_one`.
    ///
    /// - Parameters:
    ///   - logits: Marker logits from the graph, `maxOptions` long.
    ///   - action: Raw action-head outputs (softmaxed here).
    static func decision(
        logits: [Float],
        action: [Float],
        question: LayaQuestion,
        calibration: LayaCalibration
    ) throws -> LayaDecision {
        guard logits.allSatisfy(\.isFinite), action.allSatisfy(\.isFinite) else {
            throw LayaError.model("Non-finite Core ML outputs")
        }
        let k = question.optionCount
        guard k >= 1, logits.count >= k, !action.isEmpty else {
            throw LayaError.model("Model returned \(logits.count) logits for \(k) options.")
        }
        let act = LayaMath.softmax(action.map(Double.init))
        let scale = max(1e-3, calibration.scale(kind: question.kind, optionCount: k))
        let z = logits.prefix(k).map { Double($0) / scale }
        let p = LayaMath.softmax(z)

        var confidence = LayaMath.round4(LayaMath.confidence(p, optionCount: k))
        let answer: LayaAnswer
        switch question {
        case .choice(_, let options):
            let best = p.indices.max { p[$0] < p[$1] } ?? 0
            answer = .choice(
                label: options[best].label,
                probabilities: zip(options, p).map {
                    LayaLabeledProbability(label: $0.label, probability: LayaMath.round4($1))
                }
            )
        case .score(_, let levels):
            let value = p.enumerated().reduce(0.0) { $0 + Double($1.offset) * $1.element }
            answer = .score(
                value: LayaMath.round4(value),
                probabilities: p.map(LayaMath.round4),
                legend: levels
            )
        case .noul:
            let yes = p[1]
            answer = .noul(probability: LayaMath.round4(yes))
            confidence = LayaMath.round4(max(yes, 1 - yes))
        }
        return LayaDecision(
            kind: question.kind,
            answer: answer,
            confidence: confidence,
            actProbability: LayaMath.round4(act[0])
        )
    }
}
