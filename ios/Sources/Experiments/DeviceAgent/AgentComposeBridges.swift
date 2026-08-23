import MessageUI
import SwiftUI
import WebKit

struct AgentBrowserPane: UIViewRepresentable {
    let url: URL?
    var onTitleChange: ((String) -> Void)?

    func makeUIView(context: Context) -> WKWebView {
        let webView = WKWebView()
        webView.navigationDelegate = context.coordinator
        return webView
    }

    func updateUIView(_ webView: WKWebView, context: Context) {
        context.coordinator.parent = self
        guard let url else { return }
        if context.coordinator.loadedURL != url {
            context.coordinator.loadedURL = url
            webView.load(URLRequest(url: url))
        }
    }

    func makeCoordinator() -> Coordinator {
        Coordinator(parent: self)
    }

    final class Coordinator: NSObject, WKNavigationDelegate {
        var parent: AgentBrowserPane
        var loadedURL: URL?

        init(parent: AgentBrowserPane) {
            self.parent = parent
        }

        func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
            let title = webView.title?.trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
            if !title.isEmpty {
                parent.onTitleChange?(title)
            }
        }
    }
}

struct AgentSMSComposer: UIViewControllerRepresentable {
    let draft: AgentSMSDraft
    var onFinish: () -> Void

    func makeUIViewController(context: Context) -> MFMessageComposeViewController {
        let controller = MFMessageComposeViewController()
        controller.messageComposeDelegate = context.coordinator
        controller.recipients = draft.recipients
        controller.body = draft.body
        return controller
    }

    func updateUIViewController(_ uiViewController: MFMessageComposeViewController, context: Context) {}

    func makeCoordinator() -> Coordinator {
        Coordinator(onFinish: onFinish)
    }

    final class Coordinator: NSObject, MFMessageComposeViewControllerDelegate {
        let onFinish: () -> Void
        init(onFinish: @escaping () -> Void) { self.onFinish = onFinish }

        func messageComposeViewController(
            _ controller: MFMessageComposeViewController,
            didFinishWith result: MessageComposeResult
        ) {
            controller.dismiss(animated: true)
            onFinish()
        }
    }
}

struct AgentMailComposer: UIViewControllerRepresentable {
    let draft: AgentMailDraft
    var onFinish: () -> Void

    func makeUIViewController(context: Context) -> MFMailComposeViewController {
        let controller = MFMailComposeViewController()
        controller.mailComposeDelegate = context.coordinator
        controller.setToRecipients(draft.to)
        controller.setSubject(draft.subject)
        controller.setMessageBody(draft.body, isHTML: false)
        return controller
    }

    func updateUIViewController(_ uiViewController: MFMailComposeViewController, context: Context) {}

    func makeCoordinator() -> Coordinator {
        Coordinator(onFinish: onFinish)
    }

    final class Coordinator: NSObject, MFMailComposeViewControllerDelegate {
        let onFinish: () -> Void
        init(onFinish: @escaping () -> Void) { self.onFinish = onFinish }

        func mailComposeController(
            _ controller: MFMailComposeViewController,
            didFinishWith result: MFMailComposeResult,
            error: Error?
        ) {
            controller.dismiss(animated: true)
            onFinish()
        }
    }
}
