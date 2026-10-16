import SwiftUI
import simd

/// A labeled slider that shows its formatted value.
struct VRSliderRow: View {
    let title: String
    @Binding var value: Float
    let range: ClosedRange<Float>
    let step: Float
    let format: (Float) -> String

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            LabeledContent(title) {
                Text(format(value))
                    .monospacedDigit()
            }
            Slider(value: $value, in: range, step: step) {
                Text(title)
            }
            .accessibilityValue(format(value))
        }
    }
}

// MARK: - Viewer

struct PhoneVRViewerView: View {
    @ObservedObject var store: PhoneVRStore
    let screen: VRPhoneScreen
    @State private var confirmingReset = false

    private var profile: VRViewerProfile { store.settings.profile }
    private var layout: VRStereoLayout { VRStereoLayout(screen: screen, profile: profile) }
    private var ranges: VRViewerProfile.Ranges { VRViewerProfile.ranges }

    private func millimeters(_ keyPath: WritableKeyPath<VRViewerProfile, Float>) -> Binding<Float> {
        Binding(
            get: { store.settings.profile[keyPath: keyPath] * 1000 },
            set: { store.settings.profile[keyPath: keyPath] = $0 / 1000 }
        )
    }

    private func scaled(_ range: ClosedRange<Float>) -> ClosedRange<Float> {
        (range.lowerBound * 1000)...(range.upperBound * 1000)
    }

    var body: some View {
        let report = VRViewerReport(layout: layout)
        Form {
            Section {
                VRLensPreview(layout: layout)
                    .padding(.vertical, 4)
            }

            Section("In numbers") {
                LabeledContent("Each eye's field", value: String(format: "%.0f px, %.1f mm across", report.fieldDiameterPixels, report.fieldDiameterMillimeters))
                LabeledContent("Lens axis inboard", value: String(format: "%.0f px, %.1f mm", report.lensInboardPixels, report.lensInboardMillimeters))
                LabeledContent("Centre sharpness", value: String(format: "%.1f px per degree", report.displayPixelsPerDegree))
                LabeledContent("Eye to screen", value: String(format: "%.0f mm", report.eyeToScreenMillimeters))
                if let image = report.virtualImageMeters {
                    LabeledContent("Focus distance", value: String(format: "%.2f m", image))
                }
            }

            Section("Distortion") {
                VRSliderRow(title: "k1", value: $store.settings.profile.distortionK1, range: ranges.distortionK1, step: 0.005) { String(format: "%.3f", $0) }
                VRSliderRow(title: "k2", value: $store.settings.profile.distortionK2, range: ranges.distortionK2, step: 0.005) { String(format: "%.3f", $0) }
            }

            Section("Lateral color") {
                VRSliderRow(title: "Red scale", value: $store.settings.profile.redScale, range: ranges.chromaticScale, step: 0.0005) { String(format: "%.4f", $0) }
                VRSliderRow(title: "Blue scale", value: $store.settings.profile.blueScale, range: ranges.chromaticScale, step: 0.0005) { String(format: "%.4f", $0) }
                Button("Estimate from lens geometry") {
                    let estimate = VRViewerProfile.estimatedChromaticScales(
                        screenToLens: profile.screenToLensDistance,
                        eyeRelief: profile.eyeRelief,
                        focalLength: profile.lensFocalLength
                    )
                    store.settings.profile.redScale = estimate.red
                    store.settings.profile.blueScale = estimate.blue
                }
            }

            Section("Geometry") {
                VRSliderRow(title: "Lens spacing", value: millimeters(\.interLensDistance), range: scaled(ranges.interLensDistance), step: 0.1) { String(format: "%.1f mm", $0) }
                VRSliderRow(title: "Screen to lens", value: millimeters(\.screenToLensDistance), range: scaled(ranges.screenToLensDistance), step: 0.1) { String(format: "%.1f mm", $0) }
                VRSliderRow(title: "Eye relief", value: millimeters(\.eyeRelief), range: scaled(ranges.eyeRelief), step: 0.5) { String(format: "%.1f mm", $0) }
                VRSliderRow(title: "Lens focal length", value: millimeters(\.lensFocalLength), range: scaled(ranges.lensFocalLength), step: 0.5) { String(format: "%.1f mm", $0) }
                VRSliderRow(
                    title: "Field of view",
                    value: Binding(get: { profile.fieldOfView.maximum }, set: { store.settings.profile.fieldOfView = .symmetric($0) }),
                    range: ranges.fieldAngle,
                    step: 0.5
                ) { String(format: "±%.1f°", $0) }
                VRSliderRow(title: "Timewarp margin", value: $store.settings.profile.timewarpMarginDegrees, range: ranges.timewarpMarginDegrees, step: 0.5) { String(format: "%.1f°", $0) }
                Picker("Lens height", selection: $store.settings.profile.verticalAlignment) {
                    Text("Centered").tag(VRViewerProfile.VerticalAlignment.center)
                    Text("From bottom").tag(VRViewerProfile.VerticalAlignment.bottom)
                    Text("From top").tag(VRViewerProfile.VerticalAlignment.top)
                }
                if profile.verticalAlignment != .center {
                    VRSliderRow(title: "Phone edge to lens axis", value: millimeters(\.trayToLensDistance), range: scaled(ranges.trayToLensDistance), step: 0.5) { String(format: "%.1f mm", $0) }
                }
            }

            Section("Phone in the viewer") {
                Picker("Rear camera", selection: $store.settings.mounting) {
                    Text("Left side").tag(VRViewerMounting.cameraLeft)
                    Text("Right side").tag(VRViewerMounting.cameraRight)
                }
                .pickerStyle(.segmented)
            }

            Section {
                Button("Reset viewer", role: .destructive) {
                    confirmingReset = true
                }
                .accessibilityIdentifier("phoneVRResetViewer")
            }
        }
        .navigationTitle("Viewer and lenses")
        .confirmationDialog("Reset the viewer to the standard profile?", isPresented: $confirmingReset, titleVisibility: .visible) {
            Button("Reset viewer", role: .destructive) {
                store.resetViewer()
            }
        } message: {
            Text("Your distortion, color, and geometry values will be replaced.")
        }
    }
}

// MARK: - Display

struct PhoneVRDisplayView: View {
    @ObservedObject var store: PhoneVRStore
    let device: PhoneVRDeviceInfo?

    var body: some View {
        Form {
            Section("Frame rate and resolution") {
                Picker("Refresh rate", selection: $store.settings.refreshRate) {
                    ForEach(PhoneVRSettings.RefreshRate.allCases) { Text($0.title).tag($0) }
                }
                Picker("Eye resolution", selection: $store.settings.eyeResolution) {
                    ForEach(PhoneVRSettings.EyeResolution.allCases) { Text($0.title).tag($0) }
                }
                Toggle("4× multisampling", isOn: $store.settings.multisampling)
                Toggle("Single-pass stereo", isOn: $store.settings.singlePassStereo)
                    .disabled(!(device?.supportsSinglePassStereo ?? false))
            }
            Section("Latency") {
                Toggle("Pose prediction", isOn: $store.settings.prediction)
                Toggle("Late latch", isOn: $store.settings.lateLatch)
                Toggle("Timewarp", isOn: $store.settings.timewarp)
            }
            Section("Image") {
                Toggle("Lateral color correction", isOn: $store.settings.chromaticCorrection)
                Toggle("Bicubic resampling", isOn: $store.settings.bicubicResampling)
            }
            Section("Diagnostics") {
                Toggle("Stats panel", isOn: $store.settings.showStats)
                Toggle("Metal performance HUD", isOn: $store.settings.metalPerformanceHUD)
            }
        }
        .navigationTitle("Display and rendering")
    }
}

// MARK: - Tracking

struct PhoneVRTrackingView: View {
    @ObservedObject var store: PhoneVRStore

    var body: some View {
        Form {
            Section("Tracking") {
                Picker("Mode", selection: $store.settings.tracking) {
                    ForEach(PhoneVRSettings.Tracking.allCases) { Text($0.title).tag($0) }
                }
                VRSliderRow(title: "Play area radius", value: $store.settings.playAreaRadius, range: 0.75...3, step: 0.25) { String(format: "%.2f m", $0) }
                VRSliderRow(title: "Eye height until the floor is found", value: $store.settings.eyeHeight, range: 1.0...2.0, step: 0.05) { String(format: "%.2f m", $0) }
            }
            Section("Comfort") {
                Picker("Snap turn", selection: $store.settings.snapTurnDegrees) {
                    Text("15°").tag(Float(15))
                    Text("30°").tag(Float(30))
                    Text("45°").tag(Float(45))
                }
                .pickerStyle(.segmented)
                VRSliderRow(title: "Walking speed", value: $store.settings.locomotionSpeed, range: 0.5...3, step: 0.1) { String(format: "%.1f m/s", $0) }
                Toggle("Narrow the view while walking", isOn: $store.settings.comfortVignette)
                Stepper(value: $store.settings.countdownSeconds, in: 0...10, step: 1) {
                    LabeledContent("Countdown", value: "\(Int(store.settings.countdownSeconds)) s")
                }
            }
            Section("Sound") {
                Toggle("Spatial audio", isOn: $store.settings.spatialAudio)
            }
        }
        .navigationTitle("Tracking and comfort")
    }
}

// MARK: - AirPods

@MainActor
final class PhoneVRAirPodsMonitor: ObservableObject {
    @Published private(set) var running = false
    @Published private(set) var connected = false
    @Published private(set) var snapshot: VRHeadphoneCrossCheck.Snapshot?
    private var source: VRHeadphoneMotionSource?
    private var timer: Timer?

    func start() {
        guard source == nil else { return }
        let source = VRHeadphoneMotionSource(ownsPhoneMotion: true)
        source.start()
        self.source = source
        running = true
        timer = Timer.scheduledTimer(withTimeInterval: 0.5, repeats: true) { [weak self] _ in
            Task { @MainActor in self?.poll() }
        }
    }

    func stop() {
        timer?.invalidate()
        timer = nil
        source?.stop()
        source = nil
        running = false
    }

    private func poll() {
        snapshot = source?.snapshot
        connected = source?.isConnected ?? false
    }
}

struct PhoneVRAirPodsView: View {
    @ObservedObject var store: PhoneVRStore
    let supported: Bool
    @StateObject private var monitor = PhoneVRAirPodsMonitor()

    var body: some View {
        Form {
            if supported {
                Section {
                    Toggle("Cross-check with AirPods", isOn: $store.settings.airPodsCrossCheck)
                }
                Section("Live check") {
                    Button(monitor.running ? "Stop" : "Start") {
                        if monitor.running { monitor.stop() } else { monitor.start() }
                    }
                    .accessibilityIdentifier("phoneVRAirPodsCheckButton")
                    if monitor.running {
                        LabeledContent("Status", value: statusText)
                        LabeledContent("AirPods", value: monitor.connected ? "Connected" : "Not connected")
                        if let snapshot = monitor.snapshot {
                            LabeledContent("Update rate", value: snapshot.updateRateHz.map { String(format: "%.0f Hz", $0) } ?? "–")
                            LabeledContent("Delay behind the phone", value: snapshot.latency.map { String(format: "%.0f ms", $0 * 1000) } ?? "–")
                            LabeledContent("Correlation", value: snapshot.correlation.map { String(format: "%.2f", $0) } ?? "–")
                            LabeledContent("Earbud turn from phone", value: snapshot.mountRotationDegrees.map { String(format: "%.0f°", simd_length($0)) } ?? "–")
                            LabeledContent("Rotation mismatch", value: snapshot.residualDegrees.map { String(format: "%.1f°", $0) } ?? "–")
                            LabeledContent("Viewer slips", value: "\(snapshot.slipCount)")
                        }
                    }
                }
            } else {
                ContentUnavailableView(
                    "AirPods head tracking unavailable",
                    systemImage: "airpodspro",
                    description: Text("This device can't read head motion from AirPods.")
                )
            }
        }
        .navigationTitle("AirPods")
        .onDisappear { monitor.stop() }
    }

    private var statusText: String {
        guard let snapshot = monitor.snapshot else { return "Starting" }
        switch snapshot.status {
        case .waitingForAirPods: return "Waiting for AirPods motion"
        case .needsMotion: return "Shake your head with the phone held to it"
        case .aligned: return "Aligned"
        }
    }
}

// MARK: - Budget

struct PhoneVRBudgetView: View {
    let summary: VRSessionSummary?
    let displayPixelsPerDegree: Float
    @State private var refreshRate = 120
    @State private var resolution = 1024

    var body: some View {
        let budget = VRFrameBudget(refreshRate: refreshRate, eyeResolution: resolution)
        Form {
            Section {
                Picker("Refresh rate", selection: $refreshRate) {
                    Text("120 Hz").tag(120)
                    Text("90 Hz").tag(90)
                    Text("60 Hz").tag(60)
                }
                .pickerStyle(.segmented)
                Picker("Eye resolution", selection: $resolution) {
                    Text("768²").tag(768)
                    Text("1024²").tag(1024)
                    Text("1280²").tag(1280)
                }
                .pickerStyle(.segmented)
            }
            Section("Targets") {
                LabeledContent("Frame interval", value: String(format: "%.2f ms", budget.frameIntervalMilliseconds))
                LabeledContent("GPU total (80%)", value: String(format: "%.1f ms", budget.gpuTotalMilliseconds))
                LabeledContent("Eye pass", value: String(format: "%.1f ms", budget.eyePassMilliseconds))
                LabeledContent("Lens correction", value: String(format: "%.1f ms", budget.finalPassMilliseconds))
                LabeledContent("CPU render thread (50%)", value: String(format: "%.1f ms", budget.cpuMilliseconds))
                LabeledContent("Eye pixels per frame", value: String(format: "%.2f MP", budget.eyeMegapixelsPerFrame))
                LabeledContent("Eye pixels per second", value: String(format: "%.0f MP/s of %.0f native", budget.eyeMegapixelsPerSecond, budget.nativePanelMegapixelsPerSecond))
                LabeledContent("Centre sampling", value: String(format: "%.1f px/° (screen %.1f)", budget.centerPixelsPerDegree, displayPixelsPerDegree))
            }
            if let summary {
                Section("Last session, measured") {
                    LabeledContent("GPU, both eyes", value: summary.eyePassMedianMilliseconds.map { String(format: "%.1f ms", $0) } ?? "–")
                    LabeledContent("GPU, lens correction", value: summary.finalPassMedianMilliseconds.map { String(format: "%.1f ms", $0) } ?? "–")
                    LabeledContent("CPU per frame", value: summary.cpuMedianMilliseconds.map { String(format: "%.1f ms", $0) } ?? "–")
                    LabeledContent("Average frame rate", value: String(format: "%.0f fps", summary.averageFrameRate))
                }
            }
        }
        .navigationTitle("Performance budget")
    }
}
