import SwiftUI
import UniformTypeIdentifiers
#if canImport(UIKit)
import UIKit
#endif

/// `FileDocument` wrapper so a JSONL payload can be saved through SwiftUI's
/// `fileExporter` (Files / iCloud Drive picker).
struct RideJSONLFileDocument: FileDocument {
    static var readableContentTypes: [UTType] { [RideJSONLExporter.contentType] }
    static var writableContentTypes: [UTType] { [RideJSONLExporter.contentType] }

    var data: Data

    init(data: Data) {
        self.data = data
    }

    init(configuration: ReadConfiguration) throws {
        guard let data = configuration.file.regularFileContents else {
            throw CocoaError(.fileReadCorruptFile)
        }
        self.data = data
    }

    func fileWrapper(configuration: WriteConfiguration) throws -> FileWrapper {
        FileWrapper(regularFileWithContents: data)
    }
}

#if canImport(UIKit)
/// Hosts a `UIDocumentPickerViewController` for exporting many ride JSONL files
/// into Files (one URL per ride). Mount with `.background` while exporting; the
/// invisible host presents the system picker and keeps staged URLs alive until
/// the picker finishes copying.
struct RideBulkFilesExporter: UIViewControllerRepresentable {
    let urls: [URL]
    @Binding var isPresented: Bool
    var onFinished: (() -> Void)?

    func makeCoordinator() -> Coordinator {
        Coordinator(isPresented: $isPresented, onFinished: onFinished)
    }

    func makeUIViewController(context: Context) -> UIViewController {
        UIViewController()
    }

    func updateUIViewController(_ uiViewController: UIViewController, context: Context) {
        context.coordinator.onFinished = onFinished
        context.coordinator.urls = urls

        if isPresented {
            context.coordinator.presentIfNeeded(from: uiViewController)
        } else {
            context.coordinator.dismissIfNeeded(from: uiViewController)
        }
    }

    final class Coordinator: NSObject, UIDocumentPickerDelegate {
        @Binding var isPresented: Bool
        var onFinished: (() -> Void)?
        var urls: [URL] = []
        private var isPresenting = false

        init(isPresented: Binding<Bool>, onFinished: (() -> Void)?) {
            _isPresented = isPresented
            self.onFinished = onFinished
        }

        func presentIfNeeded(from host: UIViewController) {
            guard !isPresenting, host.presentedViewController == nil, !urls.isEmpty else { return }
            isPresenting = true
            let picker = UIDocumentPickerViewController(forExporting: urls, asCopy: true)
            picker.delegate = self
            host.present(picker, animated: true)
        }

        func dismissIfNeeded(from host: UIViewController) {
            guard isPresenting, host.presentedViewController != nil else { return }
            host.dismiss(animated: true) { [weak self] in
                self?.isPresenting = false
            }
        }

        func documentPicker(_ controller: UIDocumentPickerViewController, didPickDocumentsAt urls: [URL]) {
            finish()
        }

        func documentPickerWasCancelled(_ controller: UIDocumentPickerViewController) {
            finish()
        }

        private func finish() {
            isPresenting = false
            isPresented = false
            onFinished?()
        }
    }
}
#endif
