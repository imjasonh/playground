import SwiftUI

/// Second experiment: a bounded tap counter. Demonstrates that adding an
/// experiment is just "a view + a catalog entry."
struct CounterView: View {
    @State private var model = CounterModel()

    var body: some View {
        VStack(spacing: 32) {
            Text("\(model.value)")
                .font(.system(size: 72, weight: .bold, design: .rounded))
                .monospacedDigit()
                .accessibilityIdentifier("counterValue")

            HStack(spacing: 24) {
                Button {
                    model.decrement()
                } label: {
                    Image(systemName: "minus.circle.fill").font(.system(size: 48))
                }
                .disabled(!model.canDecrement)
                .accessibilityIdentifier("decrementButton")

                Button {
                    model.increment()
                } label: {
                    Image(systemName: "plus.circle.fill").font(.system(size: 48))
                }
                .disabled(!model.canIncrement)
                .accessibilityIdentifier("incrementButton")
            }

            Button("Reset") {
                model.reset()
            }
            .accessibilityIdentifier("resetButton")

            Text("Range \(model.minimum)–\(model.maximum)")
                .font(.footnote)
                .foregroundStyle(.secondary)
        }
        .padding()
    }
}

#Preview {
    NavigationStack {
        CounterView()
            .navigationTitle("Counter")
    }
}
