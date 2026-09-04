import SwiftUI

/// Compact error/warning counts with SF Symbols (not “N errors” prose).
struct ArmyListIssueCountsLabel: View {
    var errors: Int
    var warnings: Int
    var style: Font = .caption

    var body: some View {
        HStack(spacing: 8) {
            if errors > 0 {
                Label("\(errors)", systemImage: "exclamationmark.octagon.fill")
                    .foregroundStyle(.red)
                    .accessibilityLabel("\(errors) \(errors == 1 ? "error" : "errors")")
            }
            if warnings > 0 {
                Label("\(warnings)", systemImage: "exclamationmark.triangle.fill")
                    .foregroundStyle(.orange)
                    .accessibilityLabel("\(warnings) \(warnings == 1 ? "warning" : "warnings")")
            }
        }
        .font(style)
        .labelStyle(.titleAndIcon)
    }
}
