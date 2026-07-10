import SwiftUI

/// In-app Nokia-style multi-tap pad. Lives entirely inside the Playground app
/// (same Bundle ID) — no Custom Keyboard extension, so no extra App ID or
/// re-signing when this experiment ships.
struct T9KeyboardDemoView: View {
    @StateObject private var model = T9DemoModel()

    var body: some View {
        VStack(alignment: .leading, spacing: 16) {
            Text(
                "Tap a key repeatedly to cycle letters (2 = a/b/c/2). " +
                "* cycles abc → Abc → ABC → 123. # inserts a space. " +
                "Long-press a key for its digit."
            )
            .font(.subheadline)
            .foregroundStyle(.secondary)

            HStack {
                Text("Mode")
                    .foregroundStyle(.secondary)
                Spacer()
                Text(model.shiftLabel)
                    .font(.caption.monospaced())
                    .padding(.horizontal, 8)
                    .padding(.vertical, 4)
                    .background(Capsule().fill(Color.primary.opacity(0.08)))
                    .accessibilityIdentifier("t9ShiftModeLabel")
            }

            HStack(alignment: .firstTextBaseline, spacing: 4) {
                Text(model.text.isEmpty ? " " : model.text)
                    .font(.title2.monospaced())
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .accessibilityIdentifier("t9DemoText")
                Text(model.pending.isEmpty ? " " : model.pending)
                    .font(.title2.monospaced().weight(.bold))
                    .foregroundStyle(.yellow)
                    .accessibilityIdentifier("t9PendingPreview")
            }
            .padding(12)
            .frame(minHeight: 56)
            .background(RoundedRectangle(cornerRadius: 8).stroke(Color.primary.opacity(0.15)))

            T9SwiftUIPadView(model: model)
                .frame(height: 280)
                .clipShape(RoundedRectangle(cornerRadius: 12))
                .accessibilityIdentifier("t9Pad")

            HStack {
                Button("Delete") { model.delete() }
                    .accessibilityIdentifier("t9DemoDeleteButton")
                Spacer()
                Button("Clear") { model.clear() }
                    .accessibilityIdentifier("t9DemoClearButton")
            }
            .buttonStyle(.bordered)

            Spacer(minLength: 0)
        }
        .padding()
        .onDisappear {
            model.commit()
        }
    }
}

// MARK: - Model

@MainActor
final class T9DemoModel: ObservableObject {
    @Published var text = ""
    @Published var pending = ""
    @Published var shiftLabel = T9ShiftMode.lowercase.label

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
