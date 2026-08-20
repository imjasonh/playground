import SwiftUI
import UniformTypeIdentifiers

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

/// `FileDocument` wrapper for a ZIP of per-ride JSONL files.
struct RideZipFileDocument: FileDocument {
    static var readableContentTypes: [UTType] { [.zip] }
    static var writableContentTypes: [UTType] { [.zip] }

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
