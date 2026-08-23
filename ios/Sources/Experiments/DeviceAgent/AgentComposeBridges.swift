import MessageUI
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
