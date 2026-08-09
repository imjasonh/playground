import Foundation
import WebKit

/// The probe page, kept outside the main-actor probe class so the loopback
/// server (which answers on its own queue) can serve it. Deliberately
/// dependency-free, so a failure means the environment is wrong rather than
/// the content.
enum RuntimeProbePage {
    static let html = """
    <!doctype html>
    <html><head><meta charset="utf-8"><title>Container Lab runtime probe</title></head>
    <body><p id="status">probe</p></body></html>
    """
}

/// Checks whether a page served from our loopback origin is cross-origin
/// isolated inside a `WKWebView`.
///
/// This is the go/no-go test for the whole webview-hosted runtime: no
/// isolation means no `SharedArrayBuffer`, which means no wasm threads, which
/// means no emulator. It runs in CI (simulator) and is surfaced in the
/// experiment UI so it can be re-checked on a real device.
@MainActor
final class CrossOriginIsolationProbe: NSObject {
    struct Result: Equatable {
        var crossOriginIsolated: Bool
        var sharedArrayBuffer: Bool
        var webAssembly: Bool
        var sharedMemory: Bool

        /// Everything the emulator needs from the page environment.
        var isRuntimeCapable: Bool {
            crossOriginIsolated && sharedArrayBuffer && webAssembly && sharedMemory
        }

        var summary: String {
            if isRuntimeCapable {
                return "Cross-origin isolated — wasm threads and shared memory available"
            }
            let missing = [
                crossOriginIsolated ? nil : "crossOriginIsolated",
                sharedArrayBuffer ? nil : "SharedArrayBuffer",
                webAssembly ? nil : "WebAssembly",
                sharedMemory ? nil : "shared WebAssembly.Memory"
            ].compactMap { $0 }
            return "Missing: " + missing.joined(separator: ", ")
        }
    }

    enum ProbeError: Error, LocalizedError {
        case navigationFailed(String)
        case timedOut
        case unreadableResult

        var errorDescription: String? {
            switch self {
            case .navigationFailed(let detail): return "Runtime page failed to load: \(detail)"
            case .timedOut: return "Runtime page timed out"
            case .unreadableResult: return "Could not read the isolation probe result"
            }
        }
    }

    private enum LoadOutcome {
        case success
        case failure(Error)
    }

    private var loadContinuation: CheckedContinuation<Void, Error>?
    private var loadToken = UUID()

    static let probeScript = """
    (function () {
      var sharedMemory = false;
      try {
        new WebAssembly.Memory({ initial: 1, maximum: 1, shared: true });
        sharedMemory = true;
      } catch (e) {
        sharedMemory = false;
      }
      return JSON.stringify({
        isolated: self.crossOriginIsolated === true,
        sab: typeof SharedArrayBuffer === "function",
        wasm: typeof WebAssembly === "object",
        sharedMemory: sharedMemory
      });
    })();
    """

    func run(url: URL, timeout: TimeInterval = 20) async throws -> Result {
        let webView = WKWebView(
            frame: CGRect(x: 0, y: 0, width: 320, height: 240),
            configuration: WKWebViewConfiguration()
        )
        webView.navigationDelegate = self

        try await load(url, in: webView, timeout: timeout)

        let raw = try await webView.evaluateJavaScript(Self.probeScript)
        guard let json = raw as? String, let data = json.data(using: .utf8) else {
            throw ProbeError.unreadableResult
        }

        struct Payload: Decodable {
            var isolated: Bool
            var sab: Bool
            var wasm: Bool
            var sharedMemory: Bool
        }
        let payload = try JSONDecoder().decode(Payload.self, from: data)
        return Result(
            crossOriginIsolated: payload.isolated,
            sharedArrayBuffer: payload.sab,
            webAssembly: payload.wasm,
            sharedMemory: payload.sharedMemory
        )
    }

    private func load(_ url: URL, in webView: WKWebView, timeout: TimeInterval) async throws {
        let token = UUID()
        loadToken = token
        startWatchdog(token: token, timeout: timeout)
        try await withCheckedThrowingContinuation { (continuation: CheckedContinuation<Void, Error>) in
            loadContinuation = continuation
            webView.load(URLRequest(url: url, cachePolicy: .reloadIgnoringLocalAndRemoteCacheData))
        }
    }

    private func startWatchdog(token: UUID, timeout: TimeInterval) {
        Task { @MainActor [weak self] in
            try? await Task.sleep(nanoseconds: UInt64(max(timeout, 1) * 1_000_000_000))
            guard let self, self.loadToken == token else { return }
            self.finishLoad(.failure(ProbeError.timedOut))
        }
    }

    private func finishLoad(_ outcome: LoadOutcome) {
        guard let continuation = loadContinuation else { return }
        loadContinuation = nil
        switch outcome {
        case .success:
            continuation.resume()
        case .failure(let error):
            continuation.resume(throwing: error)
        }
    }
}

extension CrossOriginIsolationProbe: WKNavigationDelegate {
    func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
        finishLoad(.success)
    }

    func webView(_ webView: WKWebView, didFail navigation: WKNavigation!, withError error: Error) {
        finishLoad(.failure(ProbeError.navigationFailed(error.localizedDescription)))
    }

    func webView(_ webView: WKWebView, didFailProvisionalNavigation navigation: WKNavigation!, withError error: Error) {
        finishLoad(.failure(ProbeError.navigationFailed(error.localizedDescription)))
    }
}
