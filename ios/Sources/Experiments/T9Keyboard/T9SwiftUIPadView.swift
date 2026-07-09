import SwiftUI

/// SwiftUI multi-tap pad for the in-app experiment.
///
/// The system keyboard extension keeps a UIKit `T9PadView`; this view is used
/// only inside the host app so XCUITest can open the experiment without hanging
/// on a nested UIKit accessibility tree.
struct T9SwiftUIPadView: View {
    @ObservedObject var model: T9DemoModel

    var body: some View {
        VStack(spacing: 6) {
            ForEach(Array(T9PadLayout.rows.enumerated()), id: \.offset) { _, row in
                HStack(spacing: 6) {
                    ForEach(Array(row.enumerated()), id: \.offset) { _, key in
                        keyButton(key)
                    }
                }
            }
        }
        .padding(8)
        .background(Color(white: 0.12))
    }

    @ViewBuilder
    private func keyButton(_ key: T9PadKey) -> some View {
        let emphasized = key == .star || key == .hash
        let subtitle: String = {
            if key == .star { return model.shiftLabel }
            return key.subtitle
        }()

        VStack(spacing: 2) {
            Text(key.title)
                .font(.system(size: 22, weight: .semibold))
            Text(subtitle)
                .font(.system(size: 11, weight: .medium))
                .foregroundStyle(Color.white.opacity(0.75))
        }
        .foregroundStyle(.white)
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .background(
            RoundedRectangle(cornerRadius: 10)
                .fill(Color(white: emphasized ? 0.22 : 0.28))
        )
        .contentShape(Rectangle())
        // Prefer gesture handlers over Button so a successful long-press does
        // not also fire a short tap (which would start multi-tap cycling).
        .onTapGesture { model.tap(key) }
        .onLongPressGesture(minimumDuration: 0.45) { model.longPress(key) }
        .accessibilityAddTraits(.isButton)
        .accessibilityIdentifier("t9-key-\(key.title)")
        .accessibilityLabel(key.title)
        .accessibilityHint(subtitle)
    }
}
