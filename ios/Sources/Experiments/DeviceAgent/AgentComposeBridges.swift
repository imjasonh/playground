import SwiftUI
import WebKit

struct AgentBrowserPane: UIViewRepresentable {
    @ObservedObject var session: AgentBrowserSession

    func makeUIView(context: Context) -> WKWebView {
        session.webView
    }

    func updateUIView(_ webView: WKWebView, context: Context) {
        // Navigation is driven by AgentBrowserSession / tools.
    }
}
