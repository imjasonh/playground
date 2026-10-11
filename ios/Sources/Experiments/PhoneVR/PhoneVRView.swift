import GameController
import SwiftUI

/// Phone VR's launch page: enter the headset, set up the viewer, and review
/// what the last session measured.
struct PhoneVRView: View {
    @StateObject private var store = PhoneVRStore()
    @State private var device: PhoneVRDeviceInfo?
    @State private var launch: VRLaunchRequest?
    @State private var controllerName: String?

    private var screen: VRPhoneScreen { device?.screen ?? .iPhone15Pro }
    private var layout: VRStereoLayout { VRStereoLayout(screen: screen, profile: store.settings.profile) }

    var body: some View {
        Form {
            Section {
                VRLensPreview(layout: layout)
                    .padding(.vertical, 4)
                Button {
                    enter()
                } label: {
                    Label("Enter VR", systemImage: "binoculars.fill")
                        .font(.headline)
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .disabled(device == nil || launch != nil)
                .accessibilityIdentifier("phoneVREnterButton")
                Text(statusLine)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("phoneVRStatusLine")
            }

            Section("Setup") {
                NavigationLink {
                    PhoneVRViewerView(store: store, screen: screen)
                } label: {
                    Label("Viewer and lenses", systemImage: "eyeglasses")
                }
                .accessibilityIdentifier("phoneVRViewerLink")
                NavigationLink {
                    PhoneVRDisplayView(store: store, device: device)
                } label: {
                    Label("Display and rendering", systemImage: "display")
                }
                NavigationLink {
                    PhoneVRTrackingView(store: store)
                } label: {
                    Label("Tracking and comfort", systemImage: "move.3d")
                }
                NavigationLink {
                    PhoneVRAirPodsView(store: store, supported: device?.supportsHeadphoneMotion ?? false)
                } label: {
                    Label("AirPods", systemImage: "airpodspro")
                }
                NavigationLink {
                    PhoneVRBudgetView(summary: store.lastSummary, displayPixelsPerDegree: layout.displayPixelsPerDegree)
                } label: {
                    Label("Performance budget", systemImage: "speedometer")
                }
            }

            if let summary = store.lastSummary {
                Section("Last session") {
                    PhoneVRSummaryRows(summary: summary)
                }
            }

            Section("Controls") {
                ControlRow(symbol: "eye", title: "Select", detail: "Hold your gaze on a button, tap the screen, or press A.")
                ControlRow(symbol: "arrow.down.circle", title: "Open the menu", detail: "Look down at the ring by your feet, or press Menu.")
                ControlRow(symbol: "scope", title: "Recenter", detail: "Long-press the screen, or press Options.")
                ControlRow(symbol: "xmark.circle", title: "Exit", detail: "Tap with two fingers, or choose Exit VR in the menu.")
                ControlRow(symbol: "gamecontroller", title: "Move and turn", detail: "Left stick walks, right stick or shoulders snap-turn, X shows the room, Y shows stats.")
            }

            if let device {
                Section("This device") {
                    LabeledContent("Model", value: device.modelIdentifier)
                    LabeledContent("Panel", value: "\(device.screen.widthPixels) × \(device.screen.heightPixels) px, \(Int(device.screen.pixelsPerInch)) ppi")
                    LabeledContent("Panel size", value: String(format: "%.1f × %.1f mm", device.screen.widthMeters * 1000, device.screen.heightMeters * 1000))
                    LabeledContent("Fastest refresh", value: "\(device.maximumFramesPerSecond) Hz")
                    LabeledContent("Position tracking", value: device.supportsWorldTracking ? "ARKit world tracking" : "Not available")
                    LabeledContent("LiDAR", value: device.hasLiDAR ? "Yes" : "No")
                    LabeledContent("Single-pass stereo", value: device.supportsSinglePassStereo ? "Supported" : "Not supported")
                    LabeledContent("AirPods head tracking", value: device.supportsHeadphoneMotion ? "Supported" : "Not supported")
                    if let controllerName {
                        LabeledContent("Controller", value: controllerName)
                    }
                }
            }
        }
        .background(
            VRPresenter(request: $launch) { result in
                if let result { store.record(result) }
            }
        )
        .task {
            if device == nil { device = PhoneVRDeviceInfo.current() }
            controllerName = GCController.current?.vendorName
        }
        .onReceive(NotificationCenter.default.publisher(for: .GCControllerDidBecomeCurrent)) { _ in
            controllerName = GCController.current?.vendorName
        }
        .onReceive(NotificationCenter.default.publisher(for: .GCControllerDidStopBeingCurrent)) { _ in
            controllerName = GCController.current?.vendorName
        }
    }

    private var statusLine: String {
        guard let device else { return "Checking this device…" }
        var parts: [String] = []
        let sixDoF = store.settings.tracking == .sixDoF && device.supportsWorldTracking
        parts.append(sixDoF ? "6DoF tracking" : "3DoF tracking")
        parts.append("up to \(min(store.settings.refreshRate.maximum, device.maximumFramesPerSecond)) Hz")
        let resolution = store.settings.eyeResolution
        parts.append(resolution == .automatic ? "adaptive eye resolution" : "\(resolution.title) per eye")
        if let controllerName { parts.append(controllerName) }
        if device.isPad { parts.append("made for an iPhone in a viewer") }
        return parts.joined(separator: " · ")
    }

    private func enter() {
        guard let device, launch == nil else { return }
        launch = VRLaunchRequest(settings: store.settings, device: device)
    }
}

private struct ControlRow: View {
    let symbol: String
    let title: String
    let detail: String

    var body: some View {
        Label {
            VStack(alignment: .leading, spacing: 2) {
                Text(title)
                Text(detail)
                    .font(.subheadline)
                    .foregroundStyle(.secondary)
            }
        } icon: {
            Image(systemName: symbol)
                .foregroundStyle(.tint)
        }
        .accessibilityElement(children: .combine)
    }
}

/// Measurements from a finished session.
struct PhoneVRSummaryRows: View {
    let summary: VRSessionSummary

    private func milliseconds(_ median: Double?, _ p95: Double?) -> String {
        guard let median else { return "–" }
        guard let p95 else { return String(format: "%.1f ms", median) }
        return String(format: "%.1f ms (95th %.1f)", median, p95)
    }

    var body: some View {
        LabeledContent("Duration", value: Duration.seconds(summary.duration).formatted(.units(allowed: [.minutes, .seconds], width: .abbreviated)))
        LabeledContent("Average frame rate", value: String(format: "%.0f fps", summary.averageFrameRate))
        LabeledContent("Missed frames", value: "\(summary.missedFrames) of \(summary.frames)")
        LabeledContent("GPU, both eyes", value: milliseconds(summary.eyePassMedianMilliseconds, summary.eyePassP95Milliseconds))
        LabeledContent("GPU, lens correction", value: milliseconds(summary.finalPassMedianMilliseconds, summary.finalPassP95Milliseconds))
        LabeledContent("CPU per frame", value: milliseconds(summary.cpuMedianMilliseconds, nil))
        LabeledContent("Motion to photon", value: milliseconds(summary.photonLatencyMedianMilliseconds, summary.photonLatencyP95Milliseconds))
        LabeledContent("Time in 6DoF", value: String(format: "%.0f%%", summary.sixDoFFraction * 100))
        LabeledContent("Hottest", value: ["Nominal", "Fair", "Serious", "Critical"][min(max(summary.hottestThermalLevel, 0), 3)])
        LabeledContent("Eye resolution", value: summary.lowestEyeResolution == summary.highestEyeResolution
            ? "\(summary.highestEyeResolution)²"
            : "\(summary.lowestEyeResolution)² to \(summary.highestEyeResolution)²")
        if let latency = summary.airPodsLatencyMilliseconds {
            LabeledContent("AirPods delay", value: String(format: "%.0f ms", latency))
            LabeledContent("Viewer slips", value: "\(summary.viewerSlips)")
        }
    }
}
