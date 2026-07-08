import AppKit
import Foundation
import WebKit

final class HUDViewController: NSViewController, WKNavigationDelegate, WKScriptMessageHandler, WKURLSchemeHandler {
  private var webView: WKWebView!
  private let apiClient = CursorAPIClient()
  private var mockMode = false

  override func loadView() {
    view = NSView(frame: NSRect(x: 0, y: 0, width: 2560, height: 720))
  }

  override func viewDidLoad() {
    super.viewDidLoad()
    mockMode = KeychainStore.loadAPIKey() == nil

    let config = WKWebViewConfiguration()
    config.setURLSchemeHandler(self, forURLScheme: "xeneon")
    config.preferences.setValue(true, forKey: "developerExtrasEnabled")

    let userContent = config.userContentController
    userContent.add(self, name: "xeneon")
    if let bridgeSource = loadBridgeSource() {
      let script = WKUserScript(source: bridgeSource, injectionTime: .atDocumentStart, forMainFrameOnly: true)
      userContent.addUserScript(script)
    }

    webView = WKWebView(frame: view.bounds, configuration: config)
    webView.navigationDelegate = self
    webView.autoresizingMask = [.width, .height]
    webView.setValue(false, forKey: "drawsBackground")
    view.addSubview(webView)

    reload()
  }

  func setMockMode(_ enabled: Bool) {
    mockMode = enabled
    apiClient.mockMode = enabled
  }

  func reload() {
    apiClient.apiKey = KeychainStore.loadAPIKey()
    apiClient.mockMode = mockMode || apiClient.apiKey == nil
    webView.load(URLRequest(url: URL(string: "xeneon://app/index.html")!))
  }

  func userContentController(_ userContentController: WKUserContentController, didReceive message: WKScriptMessage) {
    guard message.name == "xeneon",
          let body = message.body as? [String: Any],
          let type = body["type"] as? String
    else { return }

    switch type {
    case "openExternal":
      if let urlString = body["url"] as? String, let url = URL(string: urlString) {
        NSWorkspace.shared.open(url)
      }
    case "request":
      handleBridgeRequest(body)
    default:
      break
    }
  }

  private func handleBridgeRequest(_ body: [String: Any]) {
    let requestId = body["id"] as? String ?? UUID().uuidString
    let path = body["path"] as? String ?? "/"
    let method = (body["method"] as? String ?? "GET").uppercased()
    let payload = body["body"]

    Task {
      do {
        let result = try await apiClient.request(path: path, method: method, body: payload)
        let ok = (200..<300).contains(result.status)
        let response: [String: Any] = [
          "id": requestId,
          "ok": ok,
          "status": result.status,
          "data": result.json,
        ]
        await sendBridgeResponse(response)
      } catch {
        let response: [String: Any] = [
          "id": requestId,
          "ok": false,
          "status": 500,
          "data": [
            "error": "request_failed",
            "message": error.localizedDescription,
          ],
        ]
        await sendBridgeResponse(response)
      }
    }
  }

  @MainActor
  private func sendBridgeResponse(_ response: [String: Any]) async {
    guard let data = try? JSONSerialization.data(withJSONObject: response),
          let json = String(data: data, encoding: .utf8)
    else { return }
    let js = "window.__xeneonBridgeResolve && window.__xeneonBridgeResolve(\(json))"
    webView.evaluateJavaScript(js, completionHandler: nil)
  }

  func webView(_ webView: WKWebView, start urlSchemeTask: WKURLSchemeTask) {
    guard let url = urlSchemeTask.request.url else {
      urlSchemeTask.didFailWithError(URLError(.badURL))
      return
    }

    let path = url.path == "/" || url.path.isEmpty ? "/index.html" : url.path
    guard let fileURL = resourceURL(for: path),
          let data = try? Data(contentsOf: fileURL)
    else {
      let body = Data("Not found".utf8)
      let response = URLResponse(
        url: url,
        mimeType: "text/plain",
        expectedContentLength: body.count,
        textEncodingName: "utf-8"
      )
      urlSchemeTask.didReceive(response)
      urlSchemeTask.didReceive(body)
      urlSchemeTask.didFinish()
      return
    }

    let mime = mimeType(for: fileURL.path)
    let response = URLResponse(
      url: url,
      mimeType: mime,
      expectedContentLength: data.count,
      textEncodingName: "utf-8"
    )
    urlSchemeTask.didReceive(response)
    urlSchemeTask.didReceive(data)
    urlSchemeTask.didFinish()
  }

  func webView(_ webView: WKWebView, stop urlSchemeTask: WKURLSchemeTask) {}

  private func resourceURL(for path: String) -> URL? {
    let cleaned = path.trimmingCharacters(in: CharacterSet(charactersIn: "/"))
    let uiRoot = bundledUIRoot()
    let candidate = uiRoot.appendingPathComponent(cleaned)
    if FileManager.default.fileExists(atPath: candidate.path) {
      return candidate
    }
    return nil
  }

  private func loadBridgeSource() -> String? {
    if let url = Bundle.main.url(forResource: "Bridge", withExtension: "js"),
       let source = try? String(contentsOf: url, encoding: .utf8)
    {
      return source
    }
    let dev = packageRoot()?.appendingPathComponent("macos/Sources/XeneonCursor/Bridge.js")
    if let dev, let source = try? String(contentsOf: dev, encoding: .utf8) {
      return source
    }
    return BridgeJS.source
  }

  private func bundledUIRoot() -> URL {
    if let resourceURL = Bundle.main.resourceURL?.appendingPathComponent("ui", isDirectory: true),
       FileManager.default.fileExists(atPath: resourceURL.path)
    {
      return resourceURL
    }
    if let ui = packageRoot()?.appendingPathComponent("ui", isDirectory: true),
       FileManager.default.fileExists(atPath: ui.path)
    {
      return ui
    }
    return URL(fileURLWithPath: FileManager.default.currentDirectoryPath).appendingPathComponent("ui")
  }

  private func packageRoot() -> URL? {
    let thisFile = URL(fileURLWithPath: #filePath)
    // .../macos/Sources/XeneonCursor/HUDViewController.swift → xeneon-cursor/
    return thisFile
      .deletingLastPathComponent()
      .deletingLastPathComponent()
      .deletingLastPathComponent()
      .deletingLastPathComponent()
  }

  private func mimeType(for path: String) -> String {
    if path.hasSuffix(".html") { return "text/html" }
    if path.hasSuffix(".css") { return "text/css" }
    if path.hasSuffix(".js") { return "text/javascript" }
    if path.hasSuffix(".svg") { return "image/svg+xml" }
    if path.hasSuffix(".json") { return "application/json" }
    if path.hasSuffix(".png") { return "image/png" }
    return "application/octet-stream"
  }
}
