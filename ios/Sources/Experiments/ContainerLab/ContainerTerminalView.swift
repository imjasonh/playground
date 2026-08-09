import SwiftUI
import UIKit
import WebKit

/// The container's console. Everything inside the webview is the guest; the
/// bar underneath is the only thing Swift draws.
struct ContainerTerminalView: View {
    @ObservedObject var session: ContainerVMSession
    @Environment(\.dismiss) private var dismiss

    let imageRoot: URL?
    let title: String

    var body: some View {
        NavigationStack {
            ZStack {
                Color.black.ignoresSafeArea()
                if let url = session.runtimeURL {
                    ContainerVMWebView(url: url, configuration: session.configuration)
                        .ignoresSafeArea(edges: .bottom)
                } else {
                    ProgressView()
                        .tint(.white)
                }
            }
            .navigationTitle(title)
            .navigationBarTitleDisplayMode(.inline)
            .toolbar {
                ToolbarItem(placement: .cancellationAction) {
                    Button("Done") {
                        session.stop()
                        dismiss()
                    }
                    .accessibilityIdentifier("containerLabTerminalDoneButton")
                }
            }
            .safeAreaInset(edge: .bottom) {
                statusBar
            }
        }
        .task {
            await session.start(imageRoot: imageRoot)
        }
    }

    private var statusBar: some View {
        HStack(spacing: 8) {
            Circle()
                .fill(statusColor)
                .frame(width: 8, height: 8)
            Text(session.phase.label)
                .font(.caption)
                .foregroundStyle(.secondary)
                .lineLimit(2)
            Spacer()
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
        .background(.ultraThinMaterial)
        .accessibilityIdentifier("containerLabTerminalStatus")
    }

    private var statusColor: Color {
        switch session.phase {
        case .running: return .green
        case .booting, .starting: return .yellow
        case .exited: return .gray
        case .failed: return .red
        case .idle: return .gray
        }
    }
}

/// Thin wrapper so the emulator page keeps one webview for the whole run.
struct ContainerVMWebView: UIViewRepresentable {
    let url: URL
    let configuration: WKWebViewConfiguration

    func makeUIView(context: Context) -> WKWebView {
        let webView = WKWebView(frame: .zero, configuration: configuration)
        webView.isOpaque = false
        webView.backgroundColor = UIColor.black
        webView.scrollView.backgroundColor = UIColor.black
        webView.scrollView.bounces = false
        webView.load(URLRequest(url: url, cachePolicy: .reloadIgnoringLocalAndRemoteCacheData))
        return webView
    }

    func updateUIView(_ uiView: WKWebView, context: Context) {}
}
