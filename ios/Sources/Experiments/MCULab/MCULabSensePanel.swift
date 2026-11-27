import AVKit
import SwiftUI

/// Controls to connect to a Seeed Studio XIAO ESP32-S3 Sense recorder HTTP server,
/// filter and browse recorded 1-minute `.mov` clips by on-device audio/vision tags,
/// and stream them with `AVPlayer`.
struct MCULabSensePanel: View {
    @ObservedObject var controller: MCULabController

    private struct StreamingClipItem: Identifiable {
        let clip: MCULabSenseClip
        let url: URL
        var id: String { clip.id }
    }

    @AppStorage("mcuLab.senseServerAddress")
    private var serverAddress: String = MCULabSenseServerAddress.defaultAddress

    @State private var status: MCULabSenseStatus?
    @State private var clips: [MCULabSenseClip] = []
    @State private var selectedTag: String?
    @State private var isLoading = false
    @State private var isUpdatingRecording = false
    @State private var errorMessage: String?
    @State private var streamingClip: StreamingClipItem?

    /// If a connected BLE XIAO ESP32-S3 Sense advertised its HTTP URL in `WakeProfile.attrs`,
    /// surface a quick one-tap fill button (checking history too when multiple boards are nearby).
    private var discoveredBleURL: String? {
        if let url = controller.latestSample?.profile?.attrs?["sense.http_url"], !url.isEmpty {
            return url
        }
        return controller.history
            .compactMap { $0.profile?.attrs?["sense.http_url"] }
            .first { !$0.isEmpty }
    }

    private var availableTags: [MCULabSenseTagCount] {
        MCULabSenseTagFilter.tagCounts(in: clips)
    }

    private var filteredClips: [MCULabSenseClip] {
        MCULabSenseTagFilter.filter(clips, by: selectedTag)
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            HStack {
                Label("XIAO ESP32-S3 Sense Clips", systemImage: "video.fill")
                    .font(.subheadline.bold())
                Spacer()
                if let status {
                    Label(
                        status.recording ? "Recording" : "Paused",
                        systemImage: status.recording ? "record.circle" : "pause.circle"
                    )
                    .font(.caption.bold())
                    .foregroundStyle(status.recording ? .red : .secondary)
                    .accessibilityIdentifier("mcuLabSenseRecordingBadge")
                }
            }

            HStack(spacing: 8) {
                TextField("http://192.168.4.1", text: $serverAddress)
                    .textFieldStyle(.roundedBorder)
                    .textInputAutocapitalization(.never)
                    .autocorrectionDisabled(true)
                    .keyboardType(.URL)
                    .font(.footnote.monospaced())
                    .accessibilityIdentifier("mcuLabSenseAddressField")

                Button {
                    Task { await refreshFromServer() }
                } label: {
                    if isLoading {
                        ProgressView()
                            .frame(minWidth: 72, minHeight: 44)
                    } else {
                        Label(
                            status == nil ? "Connect" : "Refresh",
                            systemImage: status == nil ? "link" : "arrow.clockwise"
                        )
                        .frame(minHeight: 44)
                    }
                }
                .buttonStyle(.borderedProminent)
                .disabled(isLoading)
                .accessibilityIdentifier("mcuLabSenseConnectButton")
            }

            if let bleURL = discoveredBleURL, bleURL != serverAddress {
                Button {
                    serverAddress = bleURL
                    Task { await refreshFromServer() }
                } label: {
                    Label("Use BLE-advertised \(bleURL)", systemImage: "antenna.radiowaves.left.and.right")
                        .font(.caption)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("mcuLabSenseUseBleUrlButton")
            }

            if let errorMessage {
                Label(errorMessage, systemImage: "exclamationmark.triangle.fill")
                    .font(.caption)
                    .foregroundStyle(.orange)
                    .accessibilityIdentifier("mcuLabSenseError")
            }

            if let status {
                statusSummary(status)
                tagFilterBar
                clipsListSection
            } else {
                Text("Join the XIAO-S3-Sense Wi-Fi (or enter its LAN IP) and tap Connect to browse, filter by on-device tags, and stream 1-minute audio+video clips.")
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabSenseHint")
            }
        }
        .padding(12)
        .background(Color.secondary.opacity(0.1), in: RoundedRectangle(cornerRadius: 12))
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("mcuLabSensePanel")
        .sheet(item: $streamingClip) { item in
            MCULabSenseClipPlayerSheet(clip: item.clip, streamURL: item.url)
        }
    }

    @ViewBuilder
    private func statusSummary(_ status: MCULabSenseStatus) -> some View {
        VStack(alignment: .leading, spacing: 6) {
            HStack {
                Text("\(status.ssid) (\(status.ip))")
                    .font(.caption.monospaced())
                    .foregroundStyle(.secondary)
                Spacer()
                if status.sdMounted {
                    Text(
                        "\(MCULabSenseFormatting.formatBytes(status.sdFreeBytes)) free / \(MCULabSenseFormatting.formatBytes(status.sdTotalBytes))"
                    )
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabSenseSdSpace")
                } else {
                    Text("No microSD card")
                        .font(.caption)
                        .foregroundStyle(.orange)
                }
            }

            if !status.activeTags.isEmpty || !status.models.isEmpty {
                HStack(spacing: 8) {
                    if !status.activeTags.isEmpty {
                        Label(
                            "Live: \(status.activeTags.joined(separator: ", "))",
                            systemImage: "sparkles"
                        )
                        .font(.caption2)
                        .foregroundStyle(.secondary)
                    }
                    Spacer()
                    if !status.models.isEmpty {
                        Label("\(status.models.count) SD models", systemImage: "cpu")
                            .font(.caption2)
                            .foregroundStyle(.secondary)
                    }
                }
            }

            HStack(spacing: 10) {
                Button {
                    Task { await toggleRecording(!status.recording) }
                } label: {
                    Label(
                        status.recording ? "Stop Recording" : "Start Recording",
                        systemImage: status.recording ? "stop.fill" : "record.circle"
                    )
                    .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.bordered)
                .tint(status.recording ? .red : .accentColor)
                .disabled(isUpdatingRecording || !status.sdMounted)
                .accessibilityIdentifier("mcuLabSenseRecordToggleButton")
            }
        }
    }

    @ViewBuilder
    private var tagFilterBar: some View {
        let tags = availableTags
        if !tags.isEmpty {
            ScrollView(.horizontal, showsIndicators: false) {
                HStack(spacing: 6) {
                    filterChip(title: "All (\(clips.count))", isSelected: selectedTag == nil) {
                        selectedTag = nil
                    }
                    .accessibilityIdentifier("mcuLabSenseTagFilter-all")

                    ForEach(tags) { item in
                        filterChip(
                            title: "\(item.label) (\(item.count))",
                            isSelected: selectedTag == item.label
                        ) {
                            selectedTag = selectedTag == item.label ? nil : item.label
                        }
                        .accessibilityIdentifier("mcuLabSenseTagFilter-\(item.label)")
                    }
                }
                .padding(.vertical, 2)
            }
            .accessibilityIdentifier("mcuLabSenseTagFilterBar")
        }
    }

    private func filterChip(title: String, isSelected: Bool, action: @escaping () -> Void) -> some View {
        Button(action: action) {
            Text(title)
                .font(.caption.weight(isSelected ? .semibold : .regular))
                .padding(.horizontal, 10)
                .padding(.vertical, 6)
                .background(
                    isSelected ? Color.accentColor : Color.secondary.opacity(0.15),
                    in: Capsule()
                )
                .foregroundStyle(isSelected ? Color.white : Color.primary)
        }
        .buttonStyle(.plain)
    }

    @ViewBuilder
    private var clipsListSection: some View {
        let visible = filteredClips
        if clips.isEmpty {
            Text("No finalized 1-minute clips on the SD card yet. Clips appear here as soon as each 60-second recording finishes.")
                .font(.caption)
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("mcuLabSenseEmptyClips")
        } else if visible.isEmpty {
            Text("No clips matched tag \"\(selectedTag ?? "")\".")
                .font(.caption)
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("mcuLabSenseNoMatchingClips")
        } else {
            VStack(alignment: .leading, spacing: 8) {
                Text(
                    selectedTag == nil
                        ? "Recorded Clips (\(visible.count))"
                        : "Clips tagged \"\(selectedTag ?? "")\" (\(visible.count))"
                )
                .font(.caption.bold())
                .foregroundStyle(.secondary)

                ForEach(visible) { clip in
                    VStack(alignment: .leading, spacing: 6) {
                        HStack(spacing: 10) {
                            VStack(alignment: .leading, spacing: 2) {
                                Text(clip.name)
                                    .font(.footnote.monospaced())
                                    .lineLimit(1)
                                Text(
                                    "\(MCULabSenseFormatting.formatDuration(clip.durationS)) · \(MCULabSenseFormatting.formatBytes(clip.sizeBytes))"
                                )
                                .font(.caption2.monospacedDigit())
                                .foregroundStyle(.secondary)
                            }

                            Spacer()

                            Button {
                                if let baseURL = MCULabSenseServerAddress.normalize(serverAddress) {
                                    let client = MCULabSenseClient(baseURL: baseURL)
                                    streamingClip = StreamingClipItem(
                                        clip: clip,
                                        url: client.clipStreamURL(for: clip)
                                    )
                                }
                            } label: {
                                Label("Play", systemImage: "play.fill")
                                    .font(.caption.bold())
                                    .frame(minHeight: 36)
                            }
                            .buttonStyle(.borderedProminent)
                            .accessibilityIdentifier("mcuLabSensePlay-\(clip.name)")

                            Button(role: .destructive) {
                                Task { await deleteClip(clip) }
                            } label: {
                                Image(systemName: "trash")
                                    .frame(minWidth: 36, minHeight: 36)
                            }
                            .buttonStyle(.bordered)
                            .accessibilityLabel("Delete \(clip.name)")
                            .accessibilityIdentifier("mcuLabSenseDelete-\(clip.name)")
                        }

                        if !clip.tags.isEmpty {
                            ScrollView(.horizontal, showsIndicators: false) {
                                HStack(spacing: 6) {
                                    ForEach(clip.tags) { tag in
                                        Label(
                                            "\(tag.label) \(tag.confidence)%",
                                            systemImage: tag.source.systemImage
                                        )
                                        .font(.caption2)
                                        .padding(.horizontal, 7)
                                        .padding(.vertical, 3)
                                        .background(Color.secondary.opacity(0.15), in: Capsule())
                                    }
                                }
                            }
                        }
                    }
                    .padding(.vertical, 4)
                }
            }
            .accessibilityIdentifier("mcuLabSenseClipsList")
        }
    }

    @MainActor
    private func refreshFromServer() async {
        guard let baseURL = MCULabSenseServerAddress.normalize(serverAddress) else {
            errorMessage = MCULabSenseClientError.invalidAddress.errorDescription
            return
        }
        isLoading = true
        errorMessage = nil
        defer { isLoading = false }

        let client = MCULabSenseClient(baseURL: baseURL)
        do {
            async let fetchedStatus = client.fetchStatus()
            async let fetchedClips = client.fetchClips()
            let (newStatus, clipsResponse) = try await (fetchedStatus, fetchedClips)
            status = newStatus
            clips = clipsResponse.clips
            if let currentTag = selectedTag,
               !availableTags.contains(where: { $0.label == currentTag })
            {
                selectedTag = nil
            }
        } catch {
            errorMessage = "Could not reach \(baseURL.absoluteString): \(error.localizedDescription)"
        }
    }

    @MainActor
    private func toggleRecording(_ enabled: Bool) async {
        guard let baseURL = MCULabSenseServerAddress.normalize(serverAddress) else {
            errorMessage = MCULabSenseClientError.invalidAddress.errorDescription
            return
        }
        isUpdatingRecording = true
        errorMessage = nil
        defer { isUpdatingRecording = false }

        let client = MCULabSenseClient(baseURL: baseURL)
        do {
            status = try await client.setRecording(enabled)
        } catch {
            errorMessage = "Failed to update recording state: \(error.localizedDescription)"
        }
    }

    @MainActor
    private func deleteClip(_ clip: MCULabSenseClip) async {
        guard let baseURL = MCULabSenseServerAddress.normalize(serverAddress) else {
            return
        }
        errorMessage = nil
        let client = MCULabSenseClient(baseURL: baseURL)
        do {
            try await client.deleteClip(clip)
            clips.removeAll { $0.id == clip.id }
            if let updated = try? await client.fetchStatus() {
                status = updated
            }
        } catch {
            errorMessage = "Failed to delete \(clip.name): \(error.localizedDescription)"
        }
    }
}

/// Modal AVKit player sheet that streams a `.mov` clip over HTTP byte ranges from the Sense board.
private struct MCULabSenseClipPlayerSheet: View {
    let clip: MCULabSenseClip
    let streamURL: URL

    @Environment(\.dismiss) private var dismiss
    @State private var player: AVPlayer

    init(clip: MCULabSenseClip, streamURL: URL) {
        self.clip = clip
        self.streamURL = streamURL
        _player = State(initialValue: AVPlayer(url: streamURL))
    }

    var body: some View {
        NavigationStack {
            VStack(spacing: 12) {
                VideoPlayer(player: player)
                    .frame(maxWidth: .infinity, minHeight: 260)
                    .clipShape(RoundedRectangle(cornerRadius: 12))
                    .accessibilityIdentifier("mcuLabSenseVideoPlayer")

                VStack(alignment: .leading, spacing: 6) {
                    Text(clip.name)
                        .font(.subheadline.monospaced())
                    Text(
                        "\(MCULabSenseFormatting.formatDuration(clip.durationS)) · \(MCULabSenseFormatting.formatBytes(clip.sizeBytes)) · \(streamURL.absoluteString)"
                    )
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .textSelection(.enabled)

                    if !clip.tags.isEmpty {
                        ScrollView(.horizontal, showsIndicators: false) {
                            HStack(spacing: 6) {
                                ForEach(clip.tags) { tag in
                                    Label(
                                        "\(tag.label) \(tag.confidence)% @ \(MCULabSenseFormatting.formatDuration(tag.firstS))",
                                        systemImage: tag.source.systemImage
                                    )
                                    .font(.caption2)
                                    .padding(.horizontal, 8)
                                    .padding(.vertical, 4)
                                    .background(Color.secondary.opacity(0.15), in: Capsule())
                                }
                            }
                        }
                    }
                }
                .frame(maxWidth: .infinity, alignment: .leading)
                .padding(.horizontal)

                Spacer()
            }
            .padding(.top)
            .navigationTitle("Clip #\(clip.seq)")
            .navigationBarTitleDisplayMode(.inline)
            .toolbar {
                ToolbarItem(placement: .cancellationAction) {
                    Button("Done") {
                        player.pause()
                        dismiss()
                    }
                    .accessibilityIdentifier("mcuLabSensePlayerDoneButton")
                }
            }
            .onAppear {
                player.play()
            }
            .onDisappear {
                player.pause()
            }
        }
    }
}
