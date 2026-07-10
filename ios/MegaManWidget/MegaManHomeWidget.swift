import SwiftUI
import WidgetKit

@available(iOS 17.0, *)
struct MegaManEntry: TimelineEntry {
    let date: Date
    let character: MegaManCharacter
}

@available(iOS 17.0, *)
struct MegaManTimelineProvider: AppIntentTimelineProvider {
    func placeholder(in context: Context) -> MegaManEntry {
        MegaManEntry(date: Date(), character: .default)
    }

    func snapshot(for configuration: MegaManWidgetIntent, in context: Context) async -> MegaManEntry {
        MegaManEntry(date: Date(), character: configuration.character.character)
    }

    func timeline(for configuration: MegaManWidgetIntent, in context: Context) async -> Timeline<MegaManEntry> {
        // Animation is driven by timer Text views, not timeline reloads.
        Timeline(
            entries: [MegaManEntry(date: Date(), character: configuration.character.character)],
            policy: .never
        )
    }
}

@available(iOS 17.0, *)
struct MegaManHomeWidget: Widget {
    let kind = "MegaManHomeWidget"

    var body: some WidgetConfiguration {
        AppIntentConfiguration(
            kind: kind,
            intent: MegaManWidgetIntent.self,
            provider: MegaManTimelineProvider()
        ) { entry in
            MegaManWidgetEntryView(entry: entry)
                .containerBackground(for: .widget) {
                    LinearGradient(
                        colors: [
                            Color(red: 0.05, green: 0.08, blue: 0.22),
                            Color(red: 0.12, green: 0.18, blue: 0.40),
                        ],
                        startPoint: .top,
                        endPoint: .bottom
                    )
                }
        }
        .configurationDisplayName("Mega Man 2")
        .description("Walk / jump / shoot loop — pick Mega Man or a boss.")
        .supportedFamilies([.systemSmall, .systemMedium])
    }
}

@available(iOS 17.0, *)
struct MegaManWidgetEntryView: View {
    var entry: MegaManEntry
    @Environment(\.widgetFamily) private var family

    var body: some View {
        let size: CGFloat = family == .systemMedium ? 140 : 110
        VStack(spacing: 6) {
            MegaManTimerAnimationView(
                character: entry.character,
                framesPerSecond: 8,
                spriteSize: size
            )
            Text(entry.character.name)
                .font(.caption.weight(.semibold))
                .foregroundStyle(.white.opacity(0.9))
                .minimumScaleFactor(0.7)
                .lineLimit(1)
        }
        .padding(8)
    }
}
