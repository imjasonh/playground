import Foundation

/// Exports a Device Agent conversation as JSON Lines (one typed object per line),
/// wrapped in a ZIP so it’s easy to attach in chat / Files.
enum AgentConversationExporter {
    private static let filenameStampFormatter: DateFormatter = {
        let formatter = DateFormatter()
        formatter.locale = Locale(identifier: "en_US_POSIX")
        formatter.timeZone = .current
        formatter.dateFormat = "yyyy-MM-dd'T'HH-mm-ss"
        return formatter
    }()

    private struct MetaLine: Encodable {
        let type = "meta"
        var exportedAt: Date
        var mode: String
        var modelGate: String
        var modelAvailable: Bool
        var entryCount: Int
        var toolLogCount: Int
        var browserReplayCount: Int
        var extractionDiagnosticCount: Int
    }

    private struct EntryLine: Encodable {
        let type = "entry"
        var id: String
        var date: Date
        var kind: String
        var toolName: String?
        var displayText: String
        var debugDetail: String?
    }

    private struct ToolLogLine: Encodable {
        let type = "toolLog"
        var name: String
        var detail: String
    }

    private struct BrowserReplayLine: Encodable {
        let type = "browserReplay"
        var id: UUID
        var date: Date
        var action: String
        var url: String?
        var title: String?
        var detail: String?
        var pageText: String?
        var elements: [String]?
        var headings: [String]?
        var listItems: [String]?
    }

    private struct ExtractionDiagnosticLine: Encodable {
        let type = "extractionDiagnostic"
        var id: UUID
        var date: Date
        var errorCode: String
        var errorMessage: String
        var userQuestion: String
        var title: String
        var url: String
        var headings: [String]
        var listItems: [String]
        var pageText: String
        var prompt: String
        var modelGate: String
        var modelAvailable: Bool
        var rawSnapshotPrefix: String?
        var rawModelBullets: [String]?
    }

    enum ExportError: Error, Equatable {
        case encodingFailed
    }

    /// Suggested ZIP filename for sharing.
    static func filenameForZip(at date: Date = Date()) -> String {
        "device-agent-\(filenameStampFormatter.string(from: date)).jsonl.zip"
    }

    /// Inner JSONL filename inside the ZIP.
    static func filenameForJSONL(at date: Date = Date()) -> String {
        "device-agent-\(filenameStampFormatter.string(from: date)).jsonl"
    }

    /// UTF-8 JSONL bytes (newline-terminated).
    static func jsonlData(for dump: AgentConversationDump) throws -> Data {
        let encoder = JSONEncoder()
        encoder.dateEncodingStrategy = .iso8601
        encoder.outputFormatting = [.sortedKeys]

        var lines: [String] = []
        lines.append(try encodeLine(
            MetaLine(
                exportedAt: dump.exportedAt,
                mode: dump.mode,
                modelGate: dump.modelGate,
                modelAvailable: dump.modelAvailable,
                entryCount: dump.entries.count,
                toolLogCount: dump.toolLog.count,
                browserReplayCount: dump.browserReplay.count,
                extractionDiagnosticCount: dump.extractionDiagnostics.count
            ),
            encoder: encoder
        ))
        for entry in dump.entries {
            lines.append(try encodeLine(
                EntryLine(
                    id: entry.id,
                    date: entry.date,
                    kind: entry.kind,
                    toolName: entry.toolName,
                    displayText: entry.displayText,
                    debugDetail: entry.debugDetail
                ),
                encoder: encoder
            ))
        }
        for tool in dump.toolLog {
            lines.append(try encodeLine(
                ToolLogLine(name: tool.name, detail: tool.detail),
                encoder: encoder
            ))
        }
        for event in dump.browserReplay {
            lines.append(try encodeLine(
                BrowserReplayLine(
                    id: event.id,
                    date: event.date,
                    action: event.action,
                    url: event.url,
                    title: event.title,
                    detail: event.detail,
                    pageText: event.pageText,
                    elements: event.elements,
                    headings: event.headings,
                    listItems: event.listItems
                ),
                encoder: encoder
            ))
        }
        for diagnostic in dump.extractionDiagnostics {
            lines.append(try encodeLine(
                ExtractionDiagnosticLine(
                    id: diagnostic.id,
                    date: diagnostic.date,
                    errorCode: diagnostic.errorCode,
                    errorMessage: diagnostic.errorMessage,
                    userQuestion: diagnostic.userQuestion,
                    title: diagnostic.title,
                    url: diagnostic.url,
                    headings: diagnostic.headings,
                    listItems: diagnostic.listItems,
                    pageText: diagnostic.pageText,
                    prompt: diagnostic.prompt,
                    modelGate: diagnostic.modelGate,
                    modelAvailable: diagnostic.modelAvailable,
                    rawSnapshotPrefix: diagnostic.rawSnapshotPrefix,
                    rawModelBullets: diagnostic.rawModelBullets
                ),
                encoder: encoder
            ))
        }

        guard let data = lines.joined(separator: "\n").appending("\n").data(using: .utf8) else {
            throw ExportError.encodingFailed
        }
        return data
    }

    /// ZIP containing a single `.jsonl` file (stored / uncompressed entries).
    static func zipData(for dump: AgentConversationDump) throws -> Data {
        let jsonl = try jsonlData(for: dump)
        let name = filenameForJSONL(at: dump.exportedAt)
        return try RideZipArchive.data(entries: [(name: name, data: jsonl)])
    }

    private static func encodeLine<T: Encodable>(_ value: T, encoder: JSONEncoder) throws -> String {
        let data = try encoder.encode(value)
        guard let line = String(data: data, encoding: .utf8) else {
            throw ExportError.encodingFailed
        }
        return line
    }
}
