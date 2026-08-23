import Foundation
import WebKit

/// Owns the in-app `WKWebView`, injects a page bridge, and exposes drive/read APIs for tools.
@MainActor
final class AgentBrowserSession: NSObject, ObservableObject {
    static let shared = AgentBrowserSession()

    @Published private(set) var url: URL?
    @Published private(set) var title: String = ""
    @Published private(set) var isLoading = false
    @Published private(set) var lastError: String?

    let webView: WKWebView

    private var loadWaiters: [CheckedContinuation<Void, Error>] = []
    private var loadTimeoutTask: Task<Void, Never>?

    override init() {
        let config = WKWebViewConfiguration()
        config.defaultWebpagePreferences.allowsContentJavaScript = true
        let script = WKUserScript(
            source: Self.bridgeJavaScript,
            injectionTime: .atDocumentEnd,
            forMainFrameOnly: true
        )
        config.userContentController.addUserScript(script)
        webView = WKWebView(frame: .zero, configuration: config)
        super.init()
        webView.navigationDelegate = self
        webView.allowsBackForwardNavigationGestures = true
    }

    /// Load an http(s) URL and wait until navigation finishes (or fails / times out).
    func open(_ url: URL, timeoutSeconds: Double = 30) async throws {
        lastError = nil
        isLoading = true
        self.url = url
        title = url.host ?? url.absoluteString

        try await withCheckedThrowingContinuation { (continuation: CheckedContinuation<Void, Error>) in
            loadWaiters.append(continuation)
            webView.load(URLRequest(url: url))
            loadTimeoutTask?.cancel()
            loadTimeoutTask = Task { [weak self] in
                try? await Task.sleep(nanoseconds: UInt64(timeoutSeconds * 1_000_000_000))
                guard !Task.isCancelled else { return }
                await MainActor.run {
                    self?.failLoadWaiters(AgentToolError.unavailable("Timed out loading \(url.absoluteString)."))
                }
            }
        }
    }

    func snapshot(maxTextChars: Int = 3500) async throws -> String {
        try await ensureBridge()
        let capped = max(500, min(maxTextChars, 12_000))
        let raw = try await evaluate("window.__deviceAgent.snapshot(\(capped))")
        return Self.formatSnapshotPayload(raw)
    }

    func click(ref: String) async throws -> String {
        try await ensureBridge()
        let escaped = Self.jsString(ref.trimmingCharacters(in: .whitespacesAndNewlines))
        let raw = try await evaluate("window.__deviceAgent.click(\(escaped))")
        return try Self.requireOK(raw, action: "click")
    }

    func type(ref: String, text: String, submit: Bool) async throws -> String {
        try await ensureBridge()
        let refJS = Self.jsString(ref.trimmingCharacters(in: .whitespacesAndNewlines))
        let textJS = Self.jsString(text)
        let raw = try await evaluate(
            "window.__deviceAgent.type(\(refJS), \(textJS), \(submit ? "true" : "false"))"
        )
        return try Self.requireOK(raw, action: "type")
    }

    func goBack() async throws -> String {
        guard webView.canGoBack else {
            return "No back history in the in-app browser."
        }
        isLoading = true
        webView.goBack()
        // Don't hard-wait; next snapshot will reflect the page.
        return "Navigated back."
    }

    func statusSummary() -> String {
        let titleText = title.isEmpty ? "(none)" : title
        let urlText = url?.absoluteString ?? webView.url?.absoluteString ?? "(no page loaded)"
        let loading = isLoading ? "loading" : "idle"
        return "Browser title: \(titleText)\nURL: \(urlText)\nState: \(loading)"
    }

    // MARK: - Internals

    private func ensureBridge() async throws {
        let ready = try await evaluate("typeof window.__deviceAgent === 'object' ? '1' : '0'")
        if ready.trimmingCharacters(in: .whitespacesAndNewlines) == "1" {
            return
        }
        // SPA navigations or CSP-odd pages: inject once more.
        _ = try await evaluate(Self.bridgeJavaScript + "\n'ok'")
        let again = try await evaluate("typeof window.__deviceAgent === 'object' ? '1' : '0'")
        guard again.trimmingCharacters(in: .whitespacesAndNewlines) == "1" else {
            throw AgentToolError.unavailable("In-app browser bridge is not available on this page.")
        }
    }

    private func evaluate(_ javaScript: String) async throws -> String {
        try await withCheckedThrowingContinuation { continuation in
            webView.evaluateJavaScript(javaScript) { result, error in
                if let error {
                    continuation.resume(throwing: AgentToolError.unavailable(error.localizedDescription))
                    return
                }
                if let result {
                    if let string = result as? String {
                        continuation.resume(returning: string)
                    } else if let number = result as? NSNumber {
                        continuation.resume(returning: number.stringValue)
                    } else {
                        continuation.resume(returning: String(describing: result))
                    }
                } else {
                    continuation.resume(returning: "")
                }
            }
        }
    }

    private func finishLoadWaiters() {
        loadTimeoutTask?.cancel()
        loadTimeoutTask = nil
        isLoading = false
        let waiters = loadWaiters
        loadWaiters.removeAll()
        for waiter in waiters {
            waiter.resume(returning: ())
        }
    }

    private func failLoadWaiters(_ error: Error) {
        loadTimeoutTask?.cancel()
        loadTimeoutTask = nil
        isLoading = false
        lastError = error.localizedDescription
        let waiters = loadWaiters
        loadWaiters.removeAll()
        for waiter in waiters {
            waiter.resume(throwing: error)
        }
    }

    nonisolated static func jsString(_ value: String) -> String {
        let escaped = value
            .replacingOccurrences(of: "\\", with: "\\\\")
            .replacingOccurrences(of: "'", with: "\\'")
            .replacingOccurrences(of: "\n", with: "\\n")
            .replacingOccurrences(of: "\r", with: "\\r")
        return "'\(escaped)'"
    }

    nonisolated static func formatSnapshotPayload(_ raw: String) -> String {
        guard let data = raw.data(using: .utf8),
              let json = try? JSONSerialization.jsonObject(with: data) as? [String: Any]
        else {
            return raw
        }
        let pageTitle = json["title"] as? String ?? ""
        let pageURL = json["url"] as? String ?? ""
        let elements = json["elements"] as? [String] ?? []
        let text = json["text"] as? String ?? ""
        var lines: [String] = [
            "title: \(pageTitle)",
            "url: \(pageURL)",
            "elements (\(elements.count)):",
        ]
        lines.append(contentsOf: elements)
        if !text.isEmpty {
            lines.append("text:")
            lines.append(text)
        }
        return lines.joined(separator: "\n")
    }

    nonisolated static func requireOK(_ raw: String, action: String) throws -> String {
        guard let data = raw.data(using: .utf8),
              let json = try? JSONSerialization.jsonObject(with: data) as? [String: Any]
        else {
            return raw.isEmpty ? "\(action) finished." : raw
        }
        if let ok = json["ok"] as? Bool, ok {
            return "\(action) ok"
        }
        let error = json["error"] as? String ?? "failed"
        throw AgentToolError.unavailable("browser \(action): \(error)")
    }

    /// Injected into every main-frame document. Exposes snapshot/click/type with stable refs.
    nonisolated static let bridgeJavaScript: String = #"""
    (function () {
      if (window.__deviceAgent && window.__deviceAgent.__version === 1) return;
      var refs = new Map();
      var next = 1;

      function visible(el) {
        if (!el || !el.getBoundingClientRect) return false;
        var r = el.getBoundingClientRect();
        if (r.width < 2 || r.height < 2) return false;
        var st = window.getComputedStyle(el);
        if (!st || st.visibility === 'hidden' || st.display === 'none' || st.opacity === '0') return false;
        return true;
      }

      function labelOf(el) {
        var t = el.getAttribute('aria-label')
          || el.getAttribute('title')
          || el.getAttribute('placeholder')
          || el.getAttribute('alt')
          || el.getAttribute('name')
          || (el.value != null && String(el.value))
          || (el.innerText || el.textContent || '');
        return String(t).replace(/\s+/g, ' ').trim().slice(0, 90);
      }

      function kindOf(el) {
        var role = el.getAttribute('role');
        if (role) return role;
        var tag = (el.tagName || '').toLowerCase();
        if (tag === 'a') return 'link';
        if (tag === 'button') return 'button';
        if (tag === 'select') return 'combobox';
        if (tag === 'textarea') return 'textbox';
        if (tag === 'input') return (el.type || 'text');
        if (el.isContentEditable) return 'textbox';
        return tag || 'node';
      }

      window.__deviceAgent = {
        __version: 1,
        reset: function () { refs.clear(); next = 1; },
        snapshot: function (maxChars) {
          this.reset();
          var sel = 'a[href],button,input,textarea,select,[role="button"],[role="link"],[role="textbox"],[role="searchbox"],[contenteditable="true"]';
          var nodes = Array.prototype.slice.call(document.querySelectorAll(sel)).filter(visible).slice(0, 100);
          var elements = [];
          for (var i = 0; i < nodes.length; i++) {
            var el = nodes[i];
            var ref = String(next++);
            refs.set(ref, el);
            elements.push('[' + ref + '] ' + kindOf(el) + ' "' + labelOf(el).replace(/"/g, '\\"') + '"');
          }
          var bodyText = '';
          try {
            bodyText = (document.body && (document.body.innerText || document.body.textContent) || '')
              .replace(/\s+/g, ' ').trim().slice(0, maxChars || 3500);
          } catch (e) {}
          return JSON.stringify({
            title: document.title || '',
            url: location.href || '',
            elements: elements,
            text: bodyText
          });
        },
        click: function (ref) {
          var el = refs.get(String(ref));
          if (!el) return JSON.stringify({ ok: false, error: 'unknown ref ' + ref + '; call browserSnapshot first' });
          try {
            el.scrollIntoView({ block: 'center', inline: 'nearest' });
            el.focus();
            el.click();
            return JSON.stringify({ ok: true });
          } catch (e) {
            return JSON.stringify({ ok: false, error: String(e) });
          }
        },
        type: function (ref, text, submit) {
          var el = refs.get(String(ref));
          if (!el) return JSON.stringify({ ok: false, error: 'unknown ref ' + ref + '; call browserSnapshot first' });
          try {
            el.scrollIntoView({ block: 'center', inline: 'nearest' });
            el.focus();
            var value = text == null ? '' : String(text);
            if ('value' in el) {
              el.value = value;
              el.dispatchEvent(new Event('input', { bubbles: true }));
              el.dispatchEvent(new Event('change', { bubbles: true }));
            } else if (el.isContentEditable) {
              el.textContent = value;
              el.dispatchEvent(new Event('input', { bubbles: true }));
            } else {
              return JSON.stringify({ ok: false, error: 'element is not typeable' });
            }
            if (submit) {
              var form = el.form || el.closest('form');
              if (form) {
                if (typeof form.requestSubmit === 'function') form.requestSubmit();
                else form.submit();
              } else {
                el.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', bubbles: true }));
              }
            }
            return JSON.stringify({ ok: true });
          } catch (e) {
            return JSON.stringify({ ok: false, error: String(e) });
          }
        }
      };
    })();
    """#
}

extension AgentBrowserSession: WKNavigationDelegate {
    func webView(_ webView: WKWebView, didStartProvisionalNavigation navigation: WKNavigation!) {
        isLoading = true
        lastError = nil
    }

    func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
        url = webView.url
        let nextTitle = webView.title?.trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        if !nextTitle.isEmpty {
            title = nextTitle
        } else if let host = webView.url?.host {
            title = host
        }
        finishLoadWaiters()
    }

    func webView(_ webView: WKWebView, didFail navigation: WKNavigation!, withError error: Error) {
        failLoadWaiters(error)
    }

    func webView(_ webView: WKWebView, didFailProvisionalNavigation navigation: WKNavigation!, withError error: Error) {
        failLoadWaiters(error)
    }
}
