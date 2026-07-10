import SwiftUI

/// In-app live preview of the Metal Man Home Screen widget animation.
struct MegaManWidgetDemoView: View {
    private let previewSize: CGFloat = 160

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 20) {
                previewCard
                howToAdd
                techniqueNote
            }
            .padding()
        }
        .background(Color(.systemGroupedBackground))
    }

    private var previewCard: some View {
        VStack(spacing: 12) {
            Text("Metal Man")
                .font(.title2.weight(.bold))
                .accessibilityIdentifier("megamanSelectedName")

            ZStack {
                LinearGradient(
                    colors: [
                        Color(red: 0.05, green: 0.08, blue: 0.22),
                        Color(red: 0.12, green: 0.18, blue: 0.40),
                    ],
                    startPoint: .top,
                    endPoint: .bottom
                )
                MegaManTimerAnimationView(
                    character: .metalMan,
                    framesPerSecond: 8,
                    spriteSize: previewSize
                )
            }
            .frame(maxWidth: .infinity)
            .frame(height: 220)
            .clipShape(RoundedRectangle(cornerRadius: 16, style: .continuous))
            .accessibilityIdentifier("megamanAnimationPreview")

            Text("Walk → throw Metal Blade → jump loop via public timer APIs")
                .font(.footnote)
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, alignment: .leading)
        }
        .padding()
        .background(Color(.secondarySystemGroupedBackground))
        .clipShape(RoundedRectangle(cornerRadius: 16, style: .continuous))
    }

    private var howToAdd: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Add the Home Screen widget")
                .font(.headline)
            Text(
                "On iOS 17+, long-press the Home Screen → + → ImJasonH Playground → Metal Man."
            )
            .font(.subheadline)
            .foregroundStyle(.secondary)
        }
        .padding()
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(Color(.secondarySystemGroupedBackground))
        .clipShape(RoundedRectangle(cornerRadius: 16, style: .continuous))
    }

    private var techniqueNote: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("How the animation works")
                .font(.headline)
            Text(
                "Widget extensions cannot run a normal game loop. This preview (and the "
                    + "Home Screen widget) stacks opaque Metal Man sprite frames and reveals "
                    + "them with Text timer masks — the public-API approach from Bryce "
                    + "Bostwick’s “Apple’s Widget Backdoor.”"
            )
            .font(.subheadline)
            .foregroundStyle(.secondary)
        }
        .padding()
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(Color(.secondarySystemGroupedBackground))
        .clipShape(RoundedRectangle(cornerRadius: 16, style: .continuous))
    }
}

#Preview {
    NavigationStack {
        MegaManWidgetDemoView()
            .navigationTitle("Mega Man 2 Widget")
    }
}
