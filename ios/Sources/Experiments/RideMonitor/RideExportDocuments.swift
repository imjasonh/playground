import SwiftUI
import UniformTypeIdentifiers

/// Writes a JSONL payload through SwiftUI's Files and iCloud Drive exporter.
final class RideJSONLWritableDocument: WritableDocument {
    static let writableContentTypes: [UTType] = [RideJSONLExporter.contentType]

    let data: Data

    init(data: Data) {
        self.data = data
    }

    nonisolated func writer(
        configuration: sending WriteConfiguration
    ) -> sending FileWrapperDocumentWriter<Data> {
        FileWrapperDocumentWriter(configuration) { snapshot, _ in
            FileWrapper(regularFileWithContents: snapshot)
        }
    }

    @MainActor
    func snapshot(contentType: UTType) async throws -> sending Data {
        data
    }
}

/// Writes a ZIP of per-ride JSONL files through SwiftUI's file exporter.
final class RideZipWritableDocument: WritableDocument {
    static let writableContentTypes: [UTType] = [.zip]

    let data: Data

    init(data: Data) {
        self.data = data
    }

    nonisolated func writer(
        configuration: sending WriteConfiguration
    ) -> sending FileWrapperDocumentWriter<Data> {
        FileWrapperDocumentWriter(configuration) { snapshot, _ in
            FileWrapper(regularFileWithContents: snapshot)
        }
    }

    @MainActor
    func snapshot(contentType: UTType) async throws -> sending Data {
        data
    }
}
