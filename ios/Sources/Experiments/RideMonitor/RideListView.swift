import SwiftUI

/// Browses rides saved on-device by `RideStore`. Reloads on appear so a ride you
/// just recorded shows up.
struct RideListView: View {
    @State private var rides: [Ride] = []
    private let store = RideStore()

    var body: some View {
        List {
            if rides.isEmpty {
                Text("No saved rides yet. Record one from the Ride Monitor.")
                    .font(.footnote)
                    .foregroundStyle(.secondary)
            } else {
                ForEach(rides) { ride in
                    NavigationLink {
                        RideDetailView(ride: ride)
                    } label: {
                        row(for: ride)
                    }
                }
                .onDelete(perform: delete)
            }
        }
        .navigationTitle("Past rides")
        .toolbar {
            ToolbarItem(placement: .topBarLeading) { EditButton() }
            ToolbarItem(placement: .topBarTrailing) {
                if !rides.isEmpty {
                    ShareLink(
                        item: AllRidesJSONLExport(rides: rides),
                        preview: SharePreview("All rides JSONL", image: Image(systemName: "doc.text"))
                    ) {
                        Label("Export all", systemImage: "square.and.arrow.up")
                    }
                    .accessibilityIdentifier("exportAllRidesJSONLButton")
                }
            }
        }
        .onAppear { rides = store.loadAll() }
    }

    private func row(for ride: Ride) -> some View {
        VStack(alignment: .leading, spacing: 3) {
            HStack {
                Text(ride.startedAt.formatted(date: .abbreviated, time: .shortened))
                    .font(.headline)
                Spacer()
                if ride.crashCount > 0 {
                    Image(systemName: "sos").foregroundStyle(.pink)
                }
            }
            if let summary = ride.summary, !summary.isEmpty {
                Text(summary)
                    .font(.subheadline)
                    .foregroundStyle(.primary)
                    .accessibilityIdentifier("rideSummary-\(ride.id.uuidString)")
            }
            if let weather = ride.weather {
                Label(weather.displayLine, systemImage: weather.symbolName)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("rideWeather-\(ride.id.uuidString)")
            }
            Text(String(
                format: "%@ · %.2f mi · %d jolts · peak %.1fg",
                duration(ride.durationSeconds), RideUnits.miles(fromMeters: ride.distanceMeters),
                ride.joltCount, ride.peakG
            ))
            .font(.caption)
            .foregroundStyle(.secondary)
        }
    }

    private func delete(_ offsets: IndexSet) {
        for index in offsets {
            try? store.delete(rides[index])
        }
        rides.remove(atOffsets: offsets)
    }

    private func duration(_ seconds: TimeInterval) -> String {
        let total = Int(seconds)
        return String(format: "%d:%02d", total / 60, total % 60)
    }
}
