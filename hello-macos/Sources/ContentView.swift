import SwiftUI

struct ContentView: View {
    @State private var greeting = Greeting()

    var body: some View {
        VStack(spacing: 16) {
            Text(greeting.text)
                .font(.largeTitle.weight(.semibold))
                .accessibilityIdentifier("greeting-text")

            Text("A sample macOS app in the playground.")
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("greeting-subtitle")

            Text(Date.now, style: .time)
                .font(.title3.monospacedDigit())
                .accessibilityIdentifier("greeting-clock")
        }
        .padding(32)
        .frame(minWidth: 360, minHeight: 220)
    }
}

#Preview {
    ContentView()
}
