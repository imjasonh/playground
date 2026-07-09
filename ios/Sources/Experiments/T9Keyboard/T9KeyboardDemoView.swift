import SwiftUI
import UIKit

/// In-app playground for the T9 multi-tap pad, plus instructions for enabling
/// the real system keyboard extension that ships with this app.
struct T9KeyboardDemoView: View {
    @StateObject private var model = T9DemoModel()
    @FocusState private var systemFieldFocused: Bool

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 20) {
                howToEnable
                tryHere
                systemField
            }
            .padding()
        }
        .background(Color(uiColor: UIColor(white: 0.08, alpha: 1)).ignoresSafeArea())
        .onDisappear {
            model.commit()
        }
    }

    private var howToEnable: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("System keyboard")
                .font(.headline)
                .foregroundStyle(.white)
            Text(
                """
                1. Open Settings → General → Keyboard → Keyboards → Add New Keyboard…
                2. Under Third-Party Keyboards, choose “T9 Multi-tap” (ImJasonH Playground).
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
        .background(RoundedRectangle(cornerRadius: 12).fill(Color.white.opacity(0.06)))
    }

    private var tryHere: some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack {
                Text("Try it here")
                    .font(.headline)
                    .foregroundStyle(.white)
                Spacer()
                Text(model.shiftLabel)
                    .font(.caption.monospaced())
                    .padding(.horizontal, 8)
                    .padding(.vertical, 4)
                    .background(Capsule().fill(Color.white.opacity(0.12)))
                    .foregroundStyle(.white)
                    .accessibilityIdentifier("t9ShiftModeLabel")
            }

            HStack(alignment: .firstTextBaseline, spacing: 4) {
                Text(model.text.isEmpty ? " " : model.text)
                    .font(.title2.monospaced())
                    .foregroundStyle(.white)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .accessibilityIdentifier("t9DemoText")
                Text(model.pending.isEmpty ? " " : model.pending)
                    .font(.title2.monospaced().weight(.bold))
                    .foregroundStyle(.yellow)
                    .accessibilityIdentifier("t9PendingPreview")
            }
            .padding(12)
            .frame(minHeight: 56)
            .background(RoundedRectangle(cornerRadius: 8).stroke(Color.white.opacity(0.2)))

            T9PadViewRepresentable(model: model)
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
        }
        .padding()
        .background(RoundedRectangle(cornerRadius: 12).fill(Color.white.opacity(0.06)))
    }

    private var systemField: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Test with the system keyboard")
                .font(.headline)
                .foregroundStyle(.white)
            Text("After enabling T9 Multi-tap, tap below and switch to it with the globe key.")
                .font(.subheadline)
                .foregroundStyle(.secondary)
            TextField("Type here…", text: $model.systemText, axis: .vertical)
                .lineLimit(3...6)
                .padding(12)
                .background(RoundedRectangle(cornerRadius: 8).fill(Color.white.opacity(0.08)))
                .focused($systemFieldFocused)
                .accessibilityIdentifier("t9SystemTextField")
        }
        .padding()
        .background(RoundedRectangle(cornerRadius: 12).fill(Color.white.opacity(0.06)))
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

    var padEngine: T9MultiTapEngine { engine }

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

// MARK: - UIKit pad bridge

struct T9PadViewRepresentable: UIViewRepresentable {
    @ObservedObject var model: T9DemoModel

    func makeUIView(context: Context) -> T9PadView {
        let pad = T9PadView(engine: model.padEngine)
        pad.accessibilityIdentifier = "t9Pad"
        pad.isAccessibilityElement = false
        pad.onShiftModeChange = { mode in
            model.shiftLabel = mode.label
        }
        pad.onPendingChange = { pending in
            model.pending = pending
        }
        return pad
    }

    func updateUIView(_ uiView: T9PadView, context: Context) {
        uiView.refreshChrome()
    }
}

#Preview {
    NavigationStack {
        T9KeyboardDemoView()
            .navigationTitle("T9 Keyboard")
    }
}
