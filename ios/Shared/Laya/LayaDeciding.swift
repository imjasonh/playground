import Foundation

/// Answers one typed Laya question. The Army List controller uses this so tests
/// can inject a fake and the app can fall back to a greedy pick when the
/// Core ML graph is not loaded.
@MainActor
protocol LayaDeciding {
    func decide(state: String, question: LayaQuestion) async throws -> LayaDecision
}

extension LayaModelStore: LayaDeciding {
    func decide(state: String, question: LayaQuestion) async throws -> LayaDecision {
        try await predict(state: state, question: question).decision
    }
}

/// Picks the first option (or yes, or the lowest score level). The Army List
/// controller ranks options so "first" is the theme-and-points preferred move.
@MainActor
struct LayaGreedyDecider: LayaDeciding {
    func decide(state: String, question: LayaQuestion) async throws -> LayaDecision {
        try question.validate()
        switch question {
        case .choice(_, let options):
            return Self.choice(label: options[0].label, options: options, act: 1)
        case .score(_, let levels):
            return LayaDecision(
                kind: .score,
                answer: .score(value: 0, probabilities: Self.oneHot(levels.count), legend: levels),
                confidence: 1,
                actProbability: 1
            )
        case .noul:
            return LayaDecision(
                kind: .noul,
                answer: .noul(probability: 1),
                confidence: 1,
                actProbability: 1
            )
        }
    }

    /// Builds a choice decision that puts all mass on `label`.
    static func choice(label: String, options: [LayaChoiceOption], act: Double) -> LayaDecision {
        let probabilities = options.map { option in
            LayaLabeledProbability(label: option.label, probability: option.label == label ? 1 : 0)
        }
        return LayaDecision(
            kind: .choice,
            answer: .choice(label: label, probabilities: probabilities),
            confidence: 1,
            actProbability: act
        )
    }

    private static func oneHot(_ count: Int) -> [Double] {
        guard count > 0 else { return [] }
        return (0..<count).map { $0 == 0 ? 1 : 0 }
    }
}
