import Foundation

/// Shareable debug dump of an Army List chat session.
struct ArmyListChatDump: Codable, Equatable {
    var exportedAt: Date
    var mode: String
    var modelGate: String
    var modelAvailable: Bool
    var contextPercentUsed: Int
    var contextDidCompact: Bool
    var catalogVersion: String
    var list: ArmyListDocument
    var validation: ArmyListChatDumpValidation
    var entries: [ArmyListChatDumpEntry]
    var toolLog: [ArmyListChatDumpToolLog]
}

struct ArmyListChatDumpValidation: Codable, Equatable {
    var isLegal: Bool
    var totalPoints: Int
    var detachmentPointsSpent: Int
    var errors: [ArmyListChatDumpIssue]
    var warnings: [ArmyListChatDumpIssue]
}

struct ArmyListChatDumpIssue: Codable, Equatable {
    var code: String
    var severity: String
    var message: String
    var unitID: String?
}

struct ArmyListChatDumpEntry: Codable, Equatable {
    var id: String
    var date: Date
    var kind: String
    var text: String
}

struct ArmyListChatDumpToolLog: Codable, Equatable {
    var name: String
    var detail: String
}

enum ArmyListChatDumpExporter {
    private static let filenameStampFormatter: DateFormatter = {
        let formatter = DateFormatter()
        formatter.locale = Locale(identifier: "en_US_POSIX")
        formatter.timeZone = .current
        formatter.dateFormat = "yyyy-MM-dd'T'HH-mm-ss"
        return formatter
    }()

    enum ExportError: Error, Equatable {
        case encodingFailed
    }

    static func filename(at date: Date = Date()) -> String {
        "army-list-chat-\(filenameStampFormatter.string(from: date)).json"
    }

    static func jsonData(for dump: ArmyListChatDump) throws -> Data {
        let encoder = JSONEncoder()
        encoder.dateEncodingStrategy = .iso8601
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        guard let data = try? encoder.encode(dump) else {
            throw ExportError.encodingFailed
        }
        return data
    }

    static func writeFile(for dump: ArmyListChatDump) throws -> URL {
        let data = try jsonData(for: dump)
        let url = FileManager.default.temporaryDirectory.appendingPathComponent(filename(at: dump.exportedAt))
        try data.write(to: url, options: .atomic)
        return url
    }
}
