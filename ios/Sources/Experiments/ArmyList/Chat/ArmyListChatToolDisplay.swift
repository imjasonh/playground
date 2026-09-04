import Foundation

/// Compact, human-readable labels for tool rows in List chat.
enum ArmyListChatToolDisplay {
    /// One-line label shown in the collapsed tools section.
    static func label(name: String, result: String) -> String {
        let first = result
            .split(separator: "\n", omittingEmptySubsequences: false)
            .first
            .map(String.init)?
            .trimmingCharacters(in: .whitespacesAndNewlines) ?? ""

        switch name {
        case "addUnit":
            if first.hasPrefix("Added ") {
                return "addUnit · \(stripTrailingParen(String(first.dropFirst(6))))"
            }
            if first.hasPrefix("Unknown") {
                return "addUnit · unknown datasheet"
            }
            return "addUnit"
        case "removeUnit":
            if first.hasPrefix("Removed ") {
                return "removeUnit · \(String(first.dropFirst(8)).trimmingCharacters(in: CharacterSet(charactersIn: ".")))"
            }
            return "removeUnit"
        case "setUnitModels":
            if first.hasPrefix("Set ") {
                return "setUnitModels · \(String(first.dropFirst(4)).trimmingCharacters(in: CharacterSet(charactersIn: ".")))"
            }
            return "setUnitModels"
            case "seedLegalList":
                if first.hasPrefix("Seeded ") {
                    return "seedLegalList · \(String(first.prefix(72)))"
                }
                if first.hasPrefix("Named ") || first.contains("Named “") {
                    return "seedLegalList · \(String(first.prefix(72)))"
                }
                return "seedLegalList"
            case "applyRosterPlan":
                if first.hasPrefix("Applied roster") {
                    return "applyRosterPlan · \(String(first.prefix(72)))"
                }
                return "applyRosterPlan"
        case "setBattleSize":
            if first.hasPrefix("Battle size set to ") {
                return "setBattleSize · \(String(first.dropFirst("Battle size set to ".count)).trimmingCharacters(in: CharacterSet(charactersIn: ".")))"
            }
            return "setBattleSize"
        case "setDetachments":
            if first.hasPrefix("Detachments set to: ") {
                return "setDetachments · \(String(first.dropFirst("Detachments set to: ".count)).trimmingCharacters(in: CharacterSet(charactersIn: ".")))"
            }
            return "setDetachments"
        case "setListName":
            if first.hasPrefix("List renamed to ") {
                return "setListName · \(String(first.dropFirst("List renamed to ".count)).trimmingCharacters(in: CharacterSet(charactersIn: ".")))"
            }
            return "setListName"
        case "setWarlord":
            if first.hasPrefix("Warlord set to ") {
                return "setWarlord · set"
            }
            if first.hasPrefix("Cleared Warlord") {
                return "setWarlord · cleared"
            }
            return "setWarlord"
        case "attachCharacter":
            if first.hasPrefix("Attached") {
                return "attachCharacter · attached"
            }
            if first.hasPrefix("Detached") {
                return "attachCharacter · detached"
            }
            return "attachCharacter"
        case "setEnhancement":
            if first.hasPrefix("Set enhancement ") {
                return "setEnhancement · \(String(first.dropFirst("Set enhancement ".count)).trimmingCharacters(in: CharacterSet(charactersIn: ".")))"
            }
            if first.hasPrefix("Cleared enhancements") {
                return "setEnhancement · cleared"
            }
            return "setEnhancement"
        case "searchCatalog":
            if first.hasPrefix("No catalog matches") {
                return "searchCatalog · no matches"
            }
            let hits = result.split(separator: "\n", omittingEmptySubsequences: true).count
            return "searchCatalog · \(hits) hits"
        case "getListSummary":
            return "getListSummary"
        case "clearUnits":
            return "clearUnits"
        default:
            if !first.isEmpty, first.count <= 64, !first.hasPrefix("Status:") {
                return "\(name) · \(first)"
            }
            return name
        }
    }

    /// Collapsed header for a run of tool actions.
    static func groupSummary(labels: [String]) -> String {
        guard !labels.isEmpty else { return "Actions" }
        if labels.count == 1 { return labels[0] }
        let preview = labels.prefix(2).joined(separator: ", ")
        let more = labels.count - 2
        if more > 0 {
            return "\(labels.count) actions · \(preview), +\(more)"
        }
        return "\(labels.count) actions · \(preview)"
    }

    private static func stripTrailingParen(_ text: String) -> String {
        let trimmed = text.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let paren = trimmed.firstIndex(of: "(") else {
            return trimmed.trimmingCharacters(in: CharacterSet(charactersIn: "."))
        }
        return trimmed[..<paren].trimmingCharacters(in: .whitespaces)
    }
}

/// Groups consecutive tool rows so the chat UI can collapse them.
enum ArmyListChatTranscriptBlock: Identifiable, Equatable {
    case message(ArmyListChatEntry)
    case tools(id: UUID, entries: [ArmyListChatEntry])

    var id: UUID {
        switch self {
        case .message(let entry):
            return entry.id
        case .tools(let id, _):
            return id
        }
    }

    static func build(from transcript: [ArmyListChatEntry]) -> [ArmyListChatTranscriptBlock] {
        var blocks: [ArmyListChatTranscriptBlock] = []
        var toolBuffer: [ArmyListChatEntry] = []

        func flushTools() {
            guard !toolBuffer.isEmpty else { return }
            let id = toolBuffer[0].id
            blocks.append(.tools(id: id, entries: toolBuffer))
            toolBuffer = []
        }

        for entry in transcript {
            if entry.kind == .tool {
                toolBuffer.append(entry)
            } else {
                flushTools()
                blocks.append(.message(entry))
            }
        }
        flushTools()
        return blocks
    }
}
