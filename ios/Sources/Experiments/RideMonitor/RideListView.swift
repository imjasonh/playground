import SwiftUI

/// Browses rides saved on-device by `RideStore`. Reloads on appear so a ride you
/// just recorded shows up.
struct RideListView: View {
    @State private var rides: [Ride] = []
    @State private var isSavingZipFile = false
    @State private var zipExportDocument: RideZipFileDocument?
    @State private var zipExportFilename = RideJSONLExporter.filenameForAllRidesZip()
    @State private var isSavingCombinedFile = false
    @State private var combinedExportDocument: RideJSONLFileDocument?
    @State private var combinedExportFilename = RideJSONLExporter.filenameForAllRides()
    @State private var exportErrorMessage: String?
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
                    Menu {
                        Button {
                            beginZipExport()
                        } label: {
                            Label("Save ZIP…", systemImage: "doc.zipper")
                        }
                        .accessibilityIdentifier("saveAllRidesToFilesButton")

                        Button {
                            beginCombinedFileExport()
                        } label: {
                            Label("Save one JSONL…", systemImage: "doc.badge.arrow.up")
                        }
                        .accessibilityIdentifier("saveAllRidesCombinedJSONLButton")

                        ShareLink(
                            item: AllRidesJSONLExport(rides: rides),
                            preview: SharePreview(
                                "All rides JSONL",
                                image: Image(systemName: "doc.text")
                            )
                        ) {
                            Label("Share JSONL", systemImage: "square.and.arrow.up")
                        }
                        .accessibilityIdentifier("exportAllRidesJSONLButton")
                    } label: {
                        Label("Export all", systemImage: "square.and.arrow.up")
                    }
                    .accessibilityIdentifier("exportAllRidesMenu")
                }
            }
        }
        .onAppear { rides = store.loadAll() }
        .alert("Export failed", isPresented: Binding(
            get: { exportErrorMessage != nil },
            set: { if !$0 { exportErrorMessage = nil } }
        )) {
            Button("OK", role: .cancel) { exportErrorMessage = nil }
        } message: {
            Text(exportErrorMessage ?? "")
        }
        .fileExporter(
            isPresented: $isSavingZipFile,
            document: zipExportDocument,
            contentType: .zip,
            defaultFilename: zipExportFilename
        ) { result in
            if case .failure(let error) = result {
                exportErrorMessage = error.localizedDescription
            }
            zipExportDocument = nil
        }
        .fileExporter(
            isPresented: $isSavingCombinedFile,
            document: combinedExportDocument,
            contentType: RideJSONLExporter.contentType,
            defaultFilename: combinedExportFilename
        ) { result in
            if case .failure(let error) = result {
                exportErrorMessage = error.localizedDescription
            }
            combinedExportDocument = nil
        }
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

    private func beginZipExport() {
        do {
            let data = try RideJSONLExporter.zipData(for: rides)
            zipExportFilename = RideJSONLExporter.filenameForAllRidesZip()
            zipExportDocument = RideZipFileDocument(data: data)
            isSavingZipFile = true
        } catch {
            exportErrorMessage = error.localizedDescription
        }
    }

    private func beginCombinedFileExport() {
        do {
            let data = try RideJSONLExporter.data(for: rides)
            combinedExportFilename = RideJSONLExporter.filenameForAllRides()
            combinedExportDocument = RideJSONLFileDocument(data: data)
            isSavingCombinedFile = true
        } catch {
            exportErrorMessage = error.localizedDescription
        }
    }
}
