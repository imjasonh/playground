import SwiftUI

struct ContentView: View {
    @State private var greeting = Greeting()
    @Environment(\.colorScheme) private var colorScheme

    private var shortVersion: String {
        Bundle.main.object(forInfoDictionaryKey: "CFBundleShortVersionString") as? String
            ?? "—"
    }

    var body: some View {
        VStack(spacing: 20) {
            Image(systemName: "desktopcomputer")
                .font(.system(size: 44, weight: .light))
                .symbolRenderingMode(.hierarchical)
                .foregroundStyle(.tint)
                .accessibilityHidden(true)

            Text(greeting.text)
                .font(.largeTitle.weight(.semibold))
                .accessibilityAddTraits(.isHeader)
                .accessibilityIdentifier("greeting-text")

            Label("Sparkle updates · \(shortVersion)", systemImage: "arrow.triangle.2.circlepath")
                .font(.subheadline)
                .foregroundStyle(.secondary)
                .padding(.horizontal, 12)
                .padding(.vertical, 6)
                .background(Capsule().fill(Color.primary.opacity(0.06)))
                .accessibilityIdentifier("greeting-subtitle")

            TimelineView(.periodic(from: .now, by: 1)) { context in
                Text(context.date, style: .time)
                    .font(.title2.monospacedDigit().weight(.medium))
                    .foregroundStyle(.primary)
                    .accessibilityLabel("Current time")
                    .accessibilityIdentifier("greeting-clock")
            }
        }
        .padding(36)
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .background {
            LinearGradient(
                colors: [
                    Color(nsColor: .windowBackgroundColor),
                    Color.accentColor.opacity(colorScheme == .dark ? 0.12 : 0.08),
                ],
                startPoint: .top,
                endPoint: .bottom
            )
            .ignoresSafeArea()
        }
        .frame(minWidth: 380, minHeight: 240)
    }
}

#Preview {
    ContentView()
}
