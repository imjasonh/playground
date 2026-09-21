import SwiftUI

/// Last construction step: catalog/Laya/Apple Intelligence label, and Laya
/// probability bars only when Laya answered.
struct ArmyListConstructionStepView: View {
    let step: ArmyListDecisionStep

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text(step.applied)
                .font(.subheadline)
            Text(step.worker.displayName)
                .font(.caption)
                .foregroundStyle(.secondary)
            if step.worker == .laya {
                LayaDecisionBars(decision: step.decision)
            }
        }
        .accessibilityElement(children: .combine)
        .accessibilityLabel("\(step.applied), \(step.worker.displayName)")
    }
}
