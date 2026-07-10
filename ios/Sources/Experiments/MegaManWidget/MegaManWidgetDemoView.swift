import SwiftUI

/// In-app picker + live preview of the same timer-mask animation the Home Screen
/// widget uses. Add the widget via the iOS widget gallery (iOS 17+).
struct MegaManWidgetDemoView: View {
    @State private var selected = MegaManCharacter.default
    private let previewSize: CGFloat = 160

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 20) {
                previewCard
                characterPicker
                howToAdd
                techniqueNote
            }
            .padding()
        }
        .background(Color(.systemGroupedBackground))
    }

    private var previewCard: some View {
        VStack(spacing: 12) {
            Text(selected.name)
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
                    character: selected,
                    framesPerSecond: 8,
                    spriteSize: previewSize
                )
            }
            .frame(maxWidth: .infinity)
            .frame(height: 220)
            .clipShape(RoundedRectangle(cornerRadius: 16, style: .continuous))
            .accessibilityIdentifier("megamanAnimationPreview")

            Text("Walk → shoot → jump loop via public timer APIs")
                .font(.footnote)
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, alignment: .leading)
        }
        .padding()
        .background(Color(.secondarySystemGroupedBackground))
        .clipShape(RoundedRectangle(cornerRadius: 16, style: .continuous))
    }

    private var characterPicker: some View {
        VStack(alignment: .leading, spacing: 10) {
            Text("Character")
                .font(.headline)

            LazyVGrid(
                columns: [GridItem(.adaptive(minimum: 100), spacing: 10)],
                spacing: 10
            ) {
                ForEach(MegaManCharacter.all) { character in
                    Button {
                        selected = character
                    } label: {
                        VStack(spacing: 6) {
                            Image(character.frameAssetName(0))
                                .resizable()
                                .interpolation(.none)
                                .frame(width: 56, height: 56)
                                .background(Color.white)
                                .clipShape(RoundedRectangle(cornerRadius: 8, style: .continuous))
                            Text(character.name)
                                .font(.caption.weight(.semibold))
                                .lineLimit(1)
                                .minimumScaleFactor(0.7)
                        }
                        .frame(maxWidth: .infinity)
                        .padding(.vertical, 10)
                        .padding(.horizontal, 6)
                        .background(
                            selected.id == character.id
                                ? Color.accentColor.opacity(0.18)
                                : Color(.secondarySystemGroupedBackground)
                        )
                        .overlay(
                            RoundedRectangle(cornerRadius: 12, style: .continuous)
                                .strokeBorder(
                                    selected.id == character.id ? Color.accentColor : .clear,
                                    lineWidth: 2
                                )
                        )
                        .clipShape(RoundedRectangle(cornerRadius: 12, style: .continuous))
                    }
                    .buttonStyle(.plain)
                    .accessibilityIdentifier("megamanCharacter-\(character.id)")
                    .accessibilityAddTraits(selected.id == character.id ? .isSelected : [])
                }
            }
        }
    }

    private var howToAdd: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Add the Home Screen widget")
                .font(.headline)
            Text(
                "On iOS 17+, long-press the Home Screen → + → ImJasonH Playground → Mega Man 2. "
                    + "Long-press the widget to pick Mega Man or a Robot Master."
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
                    + "Home Screen widget) stacks opaque sprite frames and reveals them with "
                    + "Text timer masks — the public-API approach from Bryce Bostwick’s "
                    + "“Apple’s Widget Backdoor.” Metal Man uses frames sliced from the "
                    + "classic Mega Man 2 sheet; other characters are placeholders until "
                    + "their sheets are added the same way."
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
