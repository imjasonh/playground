import SwiftUI
import UIKit

/// Wasm Service: name an OCI reference that carries a WebAssembly module, pull
/// it, and serve it from this device over HTTP.
struct WasmServiceView: View {
    /// `ObservedObject` on the shared model, not `StateObject`: the service
    /// outlives this view on purpose, so the view observes it rather than
    /// owning it.
    @ObservedObject private var model = WasmServiceModel.shared
    @ObservedObject private var background = WasmServiceBackground.shared
    @Environment(\.scenePhase) private var scenePhase

    var body: some View {
        List {
            moduleSection
            statusSection
            if model.isServing {
                addressSection
            }
            if let summary = model.summary {
                summarySection(summary)
            }
            backgroundSection
            logSection
            aboutSection
        }
        .navigationTitle("Wasm Service")
        .navigationBarTitleDisplayMode(.inline)
        .onChange(of: scenePhase) { phase in
            switch phase {
            case .active: model.applicationDidBecomeActive()
            case .inactive, .background: model.applicationWillResignActive()
            @unknown default: break
            }
        }
    }

    // MARK: - Sections

    private var moduleSection: some View {
        Section("Module") {
            TextField(WasmServiceModel.defaultReference, text: $model.referenceText)
                .textInputAutocapitalization(.never)
                .autocorrectionDisabled()
                .keyboardType(.URL)
                .font(.system(.body, design: .monospaced))
                .accessibilityIdentifier("wasmServiceReferenceField")

            HStack {
                Text("Port")
                Spacer()
                TextField("8080", text: $model.portText)
                    .keyboardType(.numberPad)
                    .multilineTextAlignment(.trailing)
                    .frame(width: 80)
                    .accessibilityIdentifier("wasmServicePortField")
            }

            Toggle("Reachable from your network", isOn: $model.reachableOnNetwork)
                .disabled(model.isServing)
                .accessibilityIdentifier("wasmServiceNetworkToggle")

            if model.isServing {
                Button(role: .destructive) {
                    model.stop()
                } label: {
                    Label("Stop serving", systemImage: "stop.circle")
                }
                .accessibilityIdentifier("wasmServiceStopButton")
            } else {
                Button {
                    Task { await model.pullAndStart() }
                } label: {
                    Label("Pull & run", systemImage: "play.circle")
                }
                .disabled(model.phase.isBusy)
                .accessibilityIdentifier("wasmServiceRunButton")
            }
        }
    }

    private var statusSection: some View {
        Section("Status") {
            LabeledContent("State", value: model.statusMessage)
                .accessibilityIdentifier("wasmServiceStatus")
            if model.isServing {
                LabeledContent("Requests served", value: "\(model.requestsServed)")
                    .accessibilityIdentifier("wasmServiceRequestCount")
            }
            if let error = model.errorMessage {
                Text(error)
                    .font(.footnote)
                    .foregroundStyle(.red)
                    .accessibilityIdentifier("wasmServiceError")
            }
        }
    }

    private var addressSection: some View {
        Section {
            ForEach(model.addresses, id: \.address) { interface in
                let url = "http://\(interface.address):\(model.portText)/"
                Button {
                    UIPasteboard.general.string = url
                } label: {
                    VStack(alignment: .leading, spacing: 2) {
                        Text(url)
                            .font(.system(.body, design: .monospaced))
                        Text(interface.kind)
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }
                }
                .buttonStyle(.plain)
            }
        } header: {
            Text("Reachable at")
        } footer: {
            Text(
                """
                Tap to copy. A Wi-Fi address works from a laptop on the same network. To reach the \
                phone from anywhere, install the Tailscale app and sign in — its tailnet address \
                appears here automatically and needs nothing from this app, because inbound \
                connections arrive on an ordinary interface. Making it public to the whole \
                internet is a job for Funnel on another node in the tailnet, not for the phone.
                """
            )
        }
    }

    private func summarySection(_ summary: WasmHTTPGuest.Summary) -> some View {
        Section("Module") {
            if let loaded = model.loadedModule {
                LabeledContent("Digest", value: String(loaded.digest.dropFirst(7).prefix(12)))
                LabeledContent("Size", value: WasmServiceModel.humanSize(Int64(loaded.byteCount)))
                LabeledContent("Media type", value: loaded.mediaType)
                if loaded.cameFromCache {
                    Text("Loaded from the on-device cache")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
            }
            LabeledContent("Linear memory", value: WasmServiceModel.humanSize(Int64(summary.memoryBytes)))
            LabeledContent("HTTP ABI", value: "v\(summary.abiVersion)")
        }
    }

    private var backgroundSection: some View {
        Section {
            Toggle("Keep the screen awake", isOn: $background.staysAwakeInForeground)
                .accessibilityIdentifier("wasmServiceAwakeToggle")
            Toggle("Keep running while charging", isOn: $background.keepAliveEnabled)
                .accessibilityIdentifier("wasmServiceKeepAliveToggle")
            if background.windowsRun > 0 {
                LabeledContent("Background windows", value: "\(background.windowsRun)")
            }
            if let error = background.lastSchedulingError {
                Text(error).font(.caption).foregroundStyle(.red)
            }
        } header: {
            Text("Running in the background")
        } footer: {
            Text(
                """
                iOS does not let an App Store app run a server permanently in the background, and \
                nothing here pretends otherwise. Foreground is unlimited — with the screen kept \
                awake and the phone on a charger, it just keeps serving. Leaving the app buys about \
                thirty seconds, and after that the service only comes back during background \
                processing windows the system schedules, which this asks for only while charging.
                """
            )
        }
    }

    private var logSection: some View {
        Section("Log") {
            if model.log.isEmpty {
                Text("Nothing yet").foregroundStyle(.secondary)
            } else {
                ForEach(Array(model.log.suffix(40).enumerated()), id: \.offset) { _, line in
                    Text(line)
                        .font(.system(.caption, design: .monospaced))
                        .textSelection(.enabled)
                }
            }
        }
    }

    private var aboutSection: some View {
        Section("How this works") {
            Text(
                """
                The reference above is an OCI artifact whose single layer is a WebAssembly module — \
                no root filesystem, nothing to exec. OCI is only how it travelled.

                The module is interpreted in-process by WasmKit. iOS grants no JIT entitlement \
                outside a web view, so interpreting is the only way to run wasm as ordinary app \
                code — which is what lets it be handed a real socket and keep running when a \
                WKWebView would have been suspended.

                WASI preview 1 has no sockets, so the app owns the listener and hands the module \
                raw HTTP/1.1 request bytes. The module gets a clock, randomness, and a log; it \
                cannot open a file or a connection.
                """
            )
            .font(.footnote)
            .foregroundStyle(.secondary)
        }
    }
}
