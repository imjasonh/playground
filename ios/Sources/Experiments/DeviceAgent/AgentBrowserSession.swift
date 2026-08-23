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
    /// Structured action log for conversation export / debugging (not screenshots).
    @Published private(set) var replay: [AgentBrowserReplayEvent] = []

    let webView: WKWebView

    private var loadWaiters: [CheckedContinuation<Void, Error>] = []
    private var loadTimeoutTask: Task<Void, Never>?
    private let maxReplayEvents = 200

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
        record(
            action: "open",
            detail: url.absoluteString,
            url: self.url?.absoluteString ?? url.absoluteString,
            title: title
        )
    }

    func snapshot(maxTextChars: Int = 3500) async throws -> String {
        try await ensureBridge()
        let capped = max(500, min(maxTextChars, 12_000))
        let raw = try await evaluate("window.__deviceAgent.snapshot(\(capped))")
        let parsed = Self.parseSnapshotJSON(raw)
        let formatted = Self.formatSnapshotPayload(raw)
        record(
            action: "snapshot",
            detail: "\(parsed?.elements.count ?? 0) elements",
            url: parsed?.url ?? url?.absoluteString,
            title: parsed?.title ?? title,
            pageText: parsed?.text,
            elements: parsed?.elements,
            headings: parsed?.headings,
            listItems: parsed?.listItems
        )
        return formatted
    }

    func click(ref: String) async throws -> String {
        try await ensureBridge()
        let trimmed = ref.trimmingCharacters(in: .whitespacesAndNewlines)
        let escaped = Self.jsString(trimmed)
        let raw = try await evaluate("window.__deviceAgent.click(\(escaped))")
        let result = try Self.requireOK(raw, action: "click")
        record(
            action: "click",
            detail: "ref=\(trimmed)",
            url: url?.absoluteString,
            title: title
        )
        return result
    }

    func type(ref: String, text: String, submit: Bool) async throws -> String {
        try await ensureBridge()
        let trimmedRef = ref.trimmingCharacters(in: .whitespacesAndNewlines)
        let refJS = Self.jsString(trimmedRef)
        let textJS = Self.jsString(text)
        let raw = try await evaluate(
            "window.__deviceAgent.type(\(refJS), \(textJS), \(submit ? "true" : "false"))"
        )
        let result = try Self.requireOK(raw, action: "type")
        record(
            action: "type",
            detail: "ref=\(trimmedRef) submit=\(submit) text=\(text.prefix(120))",
            url: url?.absoluteString,
            title: title
        )
        return result
    }

    func goBack() async throws -> String {
        guard webView.canGoBack else {
            return "No back history in the in-app browser."
        }
        isLoading = true
        webView.goBack()
        record(action: "back", url: url?.absoluteString, title: title)
        return "Navigated back."
    }

    func clearReplay() {
        replay.removeAll()
    }

    func record(
        action: String,
        detail: String? = nil,
        url: String? = nil,
        title: String? = nil,
        pageText: String? = nil,
        elements: [String]? = nil,
        headings: [String]? = nil,
        listItems: [String]? = nil
    ) {
        replay.append(
            AgentBrowserReplayEvent(
                action: action,
                url: url,
                title: title,
                detail: detail,
                pageText: pageText,
                elements: elements,
                headings: headings,
                listItems: listItems
            )
        )
        if replay.count > maxReplayEvents {
            replay.removeFirst(replay.count - maxReplayEvents)
        }
    }

    func statusSummary() -> String {
        let titleText = title.isEmpty ? "(none)" : title
        let urlText = url?.absoluteString ?? webView.url?.absoluteString ?? "(no page loaded)"
        let loading = isLoading ? "loading" : "idle"
        return "Browser title: \(titleText)\nURL: \(urlText)\nState: \(loading)"
    }

    // MARK: - Internals

    private func ensureBridge() async throws {
        let ready = try await evaluate(
            "(window.__deviceAgent && window.__deviceAgent.__version === 2) ? '1' : '0'"
        )
        if ready.trimmingCharacters(in: .whitespacesAndNewlines) == "1" {
            return
        }
        // SPA navigations or older bridge: inject / upgrade.
        _ = try await evaluate(Self.bridgeJavaScript + "\n'ok'")
        let again = try await evaluate(
            "(window.__deviceAgent && window.__deviceAgent.__version === 2) ? '1' : '0'"
        )
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

    struct ParsedSnapshot: Equatable {
        var title: String
        var url: String
        var elements: [String]
        var text: String
        var headings: [String]
        var listItems: [String]
    }

    nonisolated static func parseSnapshotJSON(_ raw: String) -> ParsedSnapshot? {
        guard let data = raw.data(using: .utf8),
              let json = try? JSONSerialization.jsonObject(with: data) as? [String: Any]
        else {
            return nil
        }
        return ParsedSnapshot(
            title: json["title"] as? String ?? "",
            url: json["url"] as? String ?? "",
            elements: json["elements"] as? [String] ?? [],
            text: json["text"] as? String ?? "",
            headings: json["headings"] as? [String] ?? [],
            listItems: json["listItems"] as? [String] ?? []
        )
    }

    nonisolated static func formatSnapshotPayload(_ raw: String) -> String {
        guard let parsed = parseSnapshotJSON(raw) else {
            return raw
        }
        var lines: [String] = [
            "title: \(parsed.title)",
            "url: \(parsed.url)",
            "elements (\(parsed.elements.count)):",
        ]
        lines.append(contentsOf: parsed.elements)
        if !parsed.headings.isEmpty {
            lines.append("headings:")
            lines.append(contentsOf: parsed.headings.map { "- \($0)" })
        }
        if !parsed.listItems.isEmpty {
            lines.append("listItems:")
            lines.append(contentsOf: parsed.listItems.map { "- \($0)" })
        }
        if !parsed.text.isEmpty {
            lines.append("text:")
            lines.append(parsed.text)
        }
        return lines.joined(separator: "\n")
    }

    /// Pull short bullets from scraped page text for the chat transcript.
    nonisolated static func pageFindingsText(
        title: String,
        url: String,
        pageText: String,
        headings: [String] = [],
        listItems: [String] = [],
        limit: Int = 8
    ) -> String {
        let bullets = pageFindingsBullets(
            headings: headings,
            listItems: listItems,
            pageText: pageText,
            limit: limit
        )
        return AgentPageExtractor.formatFindings(title: title, url: url, bullets: bullets)
    }

    nonisolated static func pageFindingsBullets(
        headings: [String] = [],
        listItems: [String] = [],
        pageText: String,
        limit: Int = 8
    ) -> [String] {
        var out: [String] = []

        func appendCandidate(_ raw: String) {
            let chunk = raw
                .replacingOccurrences(of: #"\s+"#, with: " ", options: .regularExpression)
                .trimmingCharacters(in: .whitespacesAndNewlines)
            guard chunk.count >= 8, chunk.count <= 160 else { return }
            let lower = chunk.lowercased()
            if isChromeNoise(lower) { return }
            let key = String(lower.prefix(36))
            if out.contains(where: { $0.lowercased().hasPrefix(key) }) { return }
            out.append(chunk)
        }

        for heading in headings {
            appendCandidate(heading)
            if out.count >= limit { return out }
        }
        for item in listItems {
            appendCandidate(item)
            if out.count >= limit { return out }
        }

        // Fallback: sentences from main page text only (already preferred over full-document scrape).
        let normalized = pageText
            .replacingOccurrences(of: "\r", with: "\n")
            .replacingOccurrences(of: #"\t+"#, with: " ", options: .regularExpression)
        var chunks = normalized
            .components(separatedBy: CharacterSet(charactersIn: "\n•|"))
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { $0.count >= 24 && $0.count <= 160 }
        if chunks.count < 3 {
            chunks = normalized
                .components(separatedBy: ". ")
                .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
                .filter { $0.count >= 24 && $0.count <= 160 }
                .map { $0.hasSuffix(".") ? $0 : "\($0)." }
        }
        for chunk in chunks {
            appendCandidate(chunk)
            if out.count >= limit { break }
        }
        return out
    }

    nonisolated static func isChromeNoise(_ lower: String) -> Bool {
        let needles = [
            "cookie", "accept all", "sign in", "log in", "subscribe", "newsletter",
            "privacy policy", "terms of use", "advertisement", "skip to", "menu",
            "enable javascript", "all rights reserved",
        ]
        return needles.contains { lower.contains($0) }
    }

    /// Back-compat helper used by older tests.
    nonisolated static func pageFindingsBullets(from text: String, limit: Int = 8) -> [String] {
        pageFindingsBullets(headings: [], listItems: [], pageText: text, limit: limit)
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
      if (window.__deviceAgent && window.__deviceAgent.__version === 2) return;
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

      function cleanText(value) {
        return String(value || '').replace(/\s+/g, ' ').trim();
      }

      function labelOf(el) {
        var t = el.getAttribute('aria-label')
          || el.getAttribute('title')
          || el.getAttribute('placeholder')
          || el.getAttribute('alt')
          || el.getAttribute('name')
          || (el.value != null && String(el.value))
          || (el.innerText || el.textContent || '');
        return cleanText(t).slice(0, 90);
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

      function mainRoot() {
        return document.querySelector('main, article, [role="main"], #content, .content') || document.body;
      }

      window.__deviceAgent = {
        __version: 2,
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

          var root = mainRoot();
          var headings = [];
          try {
            var hs = Array.prototype.slice.call((root || document).querySelectorAll('h1,h2,h3'));
            for (var hi = 0; hi < hs.length && headings.length < 12; hi++) {
              if (!visible(hs[hi])) continue;
              var ht = cleanText(hs[hi].innerText || hs[hi].textContent || '');
              if (ht.length >= 3 && ht.length <= 120) headings.push(ht);
            }
          } catch (e1) {}

          var listItems = [];
          try {
            var lis = Array.prototype.slice.call((root || document).querySelectorAll('li'));
            for (var li = 0; li < lis.length && listItems.length < 24; li++) {
              if (!visible(lis[li])) continue;
              var lt = cleanText(lis[li].innerText || lis[li].textContent || '');
              if (lt.length >= 12 && lt.length <= 140) listItems.push(lt);
            }
          } catch (e2) {}

          var bodyText = '';
          try {
            bodyText = cleanText((root && (root.innerText || root.textContent)) || '')
              .slice(0, maxChars || 3500);
          } catch (e3) {}

          return JSON.stringify({
            title: document.title || '',
            url: location.href || '',
            elements: elements,
            headings: headings,
            listItems: listItems,
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
