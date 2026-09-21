import SwiftUI

/// Probability bars for one Laya answer. Used by the Laya experiment and by
/// Army List while a construction step is showing.
struct LayaDecisionBars: View {
    let decision: LayaDecision

    var body: some View {
        VStack(alignment: .leading, spacing: 6) {
            switch decision.answer {
            case .choice(let label, let probabilities):
                Text(label)
                    .font(.headline)
                    .accessibilityIdentifier("layaAnswer")
                ForEach(Array(probabilities.enumerated()), id: \.offset) { _, item in
                    bar(item.label, item.probability)
                }
            case .score(let value, let probabilities, let legend):
                Text(String(format: "%.2f", value))
                    .font(.headline)
                    .accessibilityIdentifier("layaAnswer")
                ForEach(Array(probabilities.enumerated()), id: \.offset) { index, probability in
                    bar(index < legend.count ? legend[index] : "level \(index)", probability)
                }
            case .noul(let probability):
                Text(probability >= 0.5 ? "Yes" : "No")
                    .font(.headline)
                    .accessibilityIdentifier("layaAnswer")
                bar("true", probability)
                bar("false", 1 - probability)
            }
            LabeledContent("Confidence", value: LayaFormat.percent(decision.confidence))
                .font(.caption)
                .foregroundStyle(.secondary)
        }
        .accessibilityIdentifier("layaDecisionBars")
    }

    private func bar(_ label: String, _ probability: Double) -> some View {
        VStack(alignment: .leading, spacing: 2) {
            HStack {
                Text(label).lineLimit(1)
                Spacer()
                Text(LayaFormat.percent(probability)).monospacedDigit().foregroundStyle(.secondary)
            }
            .font(.subheadline)
            ProgressView(value: min(max(probability, 0), 1))
        }
    }
}
