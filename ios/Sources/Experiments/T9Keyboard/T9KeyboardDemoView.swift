import SwiftUI
import UIKit

/// In-app playground for the T9 multi-tap pad, plus instructions for enabling
/// the real system keyboard extension that ships with this app.
///
/// The demo uses a **SwiftUI** pad (not the UIKit extension pad) so XCUITest can
/// open this screen without timing out on nested UIButton accessibility trees.
struct T9KeyboardDemoView: View {
    @StateObject private var model = T9DemoModel()
    @FocusState private var systemFieldFocused: Bool

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 16) {
                howToEnable
                tryHere
                systemField
            }
            .padding()
        }
        .background(Color(.systemGroupedBackground).ignoresSafeArea())
        .onDisappear {
            model.commit()
        }
    }

    private var howToEnable: some View {
        VStack(alignment: .leading, spacing: 10) {
            Text("System keyboard")
                .font(.headline)
            Text(
                """
                1. Open Settings → General → Keyboard → Keyboards → Add New Keyboard…
                2. Under Third-Party Keyboards, choose “T9 Multi-tap” (ImJasonH).
                3. Tap it in any text field, or hold the globe key to switch.
                """
            )
            .font(.subheadline)
            .foregroundStyle(.secondary)

            Button {
                openSettings()
            } label: {
                Label("Open Settings", systemImage: "gear")
                    .frame(maxWidth: .infinity)
            }
            .buttonStyle(.borderedProminent)
            .accessibilityIdentifier("t9OpenSettingsButton")
        }
        .padding()
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(
            RoundedRectangle(cornerRadius: 14, style: .continuous)
                .fill(Color(.secondarySystemGroupedBackground))
        )
    }

    private var tryHere: some View {
        VStack(alignment: .leading, spacing: 12) {
            HStack {
                Text("Try it here")
                    .font(.headline)
                Spacer()
                Text(model.shiftLabel)
                    .font(.caption.monospaced())
                    .padding(.horizontal, 8)
                    .padding(.vertical, 4)
                    .background(Capsule().fill(Color.accentColor.opacity(0.15)))
                    .foregroundStyle(.primary)
                    .accessibilityIdentifier("t9ShiftModeLabel")
            }

            HStack(alignment: .firstTextBaseline, spacing: 4) {
                Text(model.text.isEmpty ? "Type here" : model.text)
                    .font(.title2.monospaced())
                    .foregroundStyle(model.text.isEmpty ? .tertiary : .primary)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .accessibilityLabel(model.text.isEmpty ? "Typed text, empty" : model.text)
                    .accessibilityIdentifier("t9DemoText")
                Text(model.pending.isEmpty ? "" : model.pending)
                    .font(.title2.monospaced().weight(.bold))
                    .foregroundStyle(Color.accentColor)
                    .accessibilityIdentifier("t9PendingPreview")
            }
            .padding(12)
            .frame(minHeight: 56)
            .background(
                RoundedRectangle(cornerRadius: 10, style: .continuous)
                    .fill(Color(.tertiarySystemGroupedBackground))
            )
            .overlay(
                RoundedRectangle(cornerRadius: 10, style: .continuous)
                    .strokeBorder(Color.primary.opacity(0.12))
            )

            T9SwiftUIPadView(model: model)
                .frame(height: 280)
                .clipShape(RoundedRectangle(cornerRadius: 14, style: .continuous))
                .accessibilityIdentifier("t9Pad")

            HStack {
                Button("Delete") { model.delete() }
                    .accessibilityIdentifier("t9DemoDeleteButton")
                Spacer()
                Button("Clear") { model.clear() }
                    .accessibilityIdentifier("t9DemoClearButton")
            }
            .buttonStyle(.bordered)
        }
        .padding()
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(
            RoundedRectangle(cornerRadius: 14, style: .continuous)
                .fill(Color(.secondarySystemGroupedBackground))
        )
    }

    private var systemField: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Test with the system keyboard")
                .font(.headline)
            Text("After enabling T9 Multi-tap, tap below and switch to it with the globe key.")
                .font(.subheadline)
                .foregroundStyle(.secondary)
            TextField("Type here…", text: $model.systemText, axis: .vertical)
                .lineLimit(3...6)
                .padding(12)
                .background(
                    RoundedRectangle(cornerRadius: 10, style: .continuous)
                        .fill(Color(.tertiarySystemGroupedBackground))
                )
                .focused($systemFieldFocused)
                .accessibilityIdentifier("t9SystemTextField")
        }
        .padding()
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(
            RoundedRectangle(cornerRadius: 14, style: .continuous)
                .fill(Color(.secondarySystemGroupedBackground))
        )
    }

    private func openSettings() {
        guard let url = URL(string: UIApplication.openSettingsURLString) else { return }
        UIApplication.shared.open(url)
    }
}

// MARK: - Model

@MainActor
final class T9DemoModel: ObservableObject {
    @Published var text = ""
    @Published var pending = ""
    @Published var shiftLabel = T9ShiftMode.lowercase.label
    @Published var systemText = ""

    private lazy var engine: T9MultiTapEngine = {
        T9MultiTapEngine(
            onInsert: { [weak self] chunk in
                self?.text.append(chunk)
            },
            onDeleteBackward: { [weak self] in
                guard let self, !self.text.isEmpty else { return }
                self.text.removeLast()
            },
            onStateChange: { [weak self] in
                self?.syncFromEngine()
            }
        )
    }()

    func tap(_ key: T9PadKey) {
        engine.tap(key)
    }

    func longPress(_ key: T9PadKey) {
        engine.longPress(key)
    }

    func delete() {
        engine.deleteBackward()
    }

    func clear() {
        engine.commitPending()
        text = ""
        syncFromEngine()
    }

    func commit() {
        engine.commitPending()
    }

    private func syncFromEngine() {
        pending = engine.pendingPreview
        shiftLabel = engine.shiftMode.label
    }
}

#Preview {
    NavigationStack {
        T9KeyboardDemoView()
            .navigationTitle("T9 Keyboard")
    }
}
