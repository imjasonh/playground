import SwiftUI
import WidgetKit

@available(iOS 17.0, *)
struct MegaManEntry: TimelineEntry {
    let date: Date
}

@available(iOS 17.0, *)
struct MegaManTimelineProvider: TimelineProvider {
    func placeholder(in context: Context) -> MegaManEntry {
        MegaManEntry(date: Date())
    }

    func getSnapshot(in context: Context, completion: @escaping (MegaManEntry) -> Void) {
        completion(MegaManEntry(date: Date()))
    }

    func getTimeline(in context: Context, completion: @escaping (Timeline<MegaManEntry>) -> Void) {
        // Animation is driven by timer Text views, not timeline reloads.
        completion(Timeline(entries: [MegaManEntry(date: Date())], policy: .never))
    }
}

@available(iOS 17.0, *)
struct MegaManHomeWidget: Widget {
    let kind = "MegaManHomeWidget"

    var body: some WidgetConfiguration {
        StaticConfiguration(kind: kind, provider: MegaManTimelineProvider()) { entry in
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
        .configurationDisplayName("Metal Man")
        .description("Mega Man 2 Metal Man — walk, throw, and jump loop.")
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
                character: .metalMan,
                framesPerSecond: 8,
                spriteSize: size
            )
            Text("Metal Man")
                .font(.caption.weight(.semibold))
                .foregroundStyle(.white.opacity(0.9))
                .minimumScaleFactor(0.7)
                .lineLimit(1)
        }
        .padding(8)
    }
}
