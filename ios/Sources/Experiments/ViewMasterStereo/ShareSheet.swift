import SwiftUI
import UIKit

/// Thin wrapper around `UIActivityViewController` for sharing a file URL.
struct ShareSheet: UIViewControllerRepresentable {
    let items: [Any]
    var onComplete: (() -> Void)? = nil

    func makeUIViewController(context: Context) -> UIActivityViewController {
        let controller = UIActivityViewController(activityItems: items, applicationActivities: nil)
        controller.completionWithItemsHandler = { _, _, _, _ in
            onComplete?()
        }
        if let popover = controller.popoverPresentationController {
            // Required on iPad; center of the screen is a stable fallback.
            let scene = UIApplication.shared.connectedScenes
                .compactMap { $0 as? UIWindowScene }
                .first { $0.activationState == .foregroundActive }
            let window = scene?.windows.first { $0.isKeyWindow } ?? scene?.windows.first
            popover.sourceView = window
            popover.sourceRect = window.map {
                CGRect(x: $0.bounds.midX, y: $0.bounds.midY, width: 1, height: 1)
            } ?? CGRect(x: 0, y: 0, width: 1, height: 1)
            popover.permittedArrowDirections = []
        }
        return controller
    }

    func updateUIViewController(_ uiViewController: UIActivityViewController, context: Context) {}
}
