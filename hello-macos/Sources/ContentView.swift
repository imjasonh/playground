import SwiftUI

struct ContentView: View {
    @State private var greeting = Greeting()

    private var shortVersion: String {
        Bundle.main.object(forInfoDictionaryKey: "CFBundleShortVersionString") as? String
            ?? "—"
    }

    var body: some View {
        VStack(spacing: 16) {
            Text(greeting.text)
                .font(.largeTitle.weight(.semibold))
                .accessibilityAddTraits(.isHeader)
                .accessibilityIdentifier("greeting-text")

            Text("Sparkle auto-updates enabled — you are on \(shortVersion).")
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("greeting-subtitle")

            TimelineView(.periodic(from: .now, by: 1)) { context in
                Text(context.date, style: .time)
                    .font(.title3.monospacedDigit())
                    .accessibilityLabel("Current time")
                    .accessibilityIdentifier("greeting-clock")
            }
        }
        .padding(32)
        .frame(minWidth: 360, minHeight: 220)
    }
}

#Preview {
    ContentView()
}
