import Foundation
import WebKit

/// Hosts the wasm emulator page and relays what the guest prints back to
/// SwiftUI.
///
/// The webview is where the container actually runs: WebKit's WebContent
/// process is the only place on iOS that may JIT, and QEMU Wasm leans on that
/// to compile guest basic blocks. Swift's side of the bridge is deliberately
/// narrow — the page posts progress messages, and nothing else crosses.
@MainActor
final class ContainerVMSession: NSObject, ObservableObject {
    enum Phase: Equatable {
        case idle
        case starting
        case booting
        case running
        case exited
        case failed(String)

        var label: String {
            switch self {
            case .idle: return "Idle"
            case .starting: return "Starting loopback runtime…"
            case .booting: return "Booting the guest kernel…"
            case .running: return "Running"
            case .exited: return "Guest exited"
            case .failed(let detail): return "Failed: \(detail)"
            }
        }

        var isFailure: Bool {
            if case .failed = self { return true }
            return false
        }
    }

    static let messageName = "containerLab"
    private static let maxRetainedLines = 500

    @Published private(set) var phase: Phase = .idle
    @Published private(set) var lines: [String] = []
    @Published private(set) var runtimeURL: URL?

    let configuration: WKWebViewConfiguration
    private let server: ContainerRuntimeServer

    init(server: ContainerRuntimeServer) {
        self.server = server
        self.configuration = WKWebViewConfiguration()
        super.init()
        configuration.userContentController.add(self, name: Self.messageName)
    }

    /// Brings up the loopback origin and points the webview at the runtime page.
    func start(imageRoot: URL?) async {
        guard runtimeURL == nil else { return }
        // `stop()` drops the handler to break the retain cycle the content
        // controller would otherwise hold on this session, so re-register it
        // here rather than only in `init` — otherwise a second visit to the
        // console would show a webview nothing could report back through.
        configuration.userContentController.removeScriptMessageHandler(forName: Self.messageName)
        configuration.userContentController.add(self, name: Self.messageName)
        lines.removeAll()
        phase = .starting
        do {
            let base = try await server.start(imageRoot: imageRoot)
            server.update(imageRoot: imageRoot)
            runtimeURL = base
            phase = .booting
        } catch {
            phase = .failed(ContainerLabModel.describe(error))
        }
    }

    func stop() {
        configuration.userContentController.removeScriptMessageHandler(forName: Self.messageName)
        server.stop()
        runtimeURL = nil
        phase = .idle
    }

    private func append(_ line: String) {
        let trimmed = line.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return }
        lines.append(trimmed)
        if lines.count > Self.maxRetainedLines {
            lines.removeFirst(lines.count - Self.maxRetainedLines)
        }
    }
}

extension ContainerVMSession: WKScriptMessageHandler {
    func userContentController(
        _ userContentController: WKUserContentController,
        didReceive message: WKScriptMessage
    ) {
        guard message.name == Self.messageName,
              let body = message.body as? [String: Any],
              let kind = body["kind"] as? String else { return }
        let detail = body["detail"] as? String

        switch kind {
        case "starting":
            phase = .booting
        case "ready":
            phase = .running
        case "output":
            if let detail { append(detail) }
            if phase == .booting { phase = .running }
        case "runtime-missing":
            phase = .failed("no emulator bundled (\(detail ?? "out.js")) — run ios/ContainerRuntime/fetch-runtime.sh")
        case "error":
            phase = .failed(detail ?? "unknown error")
        case "exited":
            phase = .exited
        default:
            break
        }
    }
}
