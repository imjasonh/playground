import Foundation

/// The three typed-decision shapes Laya answers. Raw values are the `qtype`
/// ids the exported model reads.
enum LayaQuestionKind: Int, CaseIterable, Codable, Equatable {
    case choice = 0
    case score = 1
    case noul = 2

    /// The prompt word (`"choice question: …"`) and the calibration key.
    var name: String {
        switch self {
        case .choice: return "choice"
        case .score: return "score"
        case .noul: return "noul"
        }
    }

    var displayName: String {
        switch self {
        case .choice: return "Choice"
        case .score: return "Score"
        case .noul: return "Yes / no"
        }
    }
}

/// One labeled option of a `choice` question.
struct LayaChoiceOption: Equatable, Codable {
    let label: String
    let description: String?

    init(_ label: String, _ description: String? = nil) {
        self.label = label
        self.description = description
    }
}

/// A typed question. Mirrors the `{"t", "ins", "crit"}` dictionary the Python
/// runtime accepts, with string criteria only.
enum LayaQuestion: Equatable {
    /// Pick one label. Options render as `label` or `label: description`.
    case choice(instructions: String, options: [LayaChoiceOption])
    /// Pick a level. Level `i` renders as `level i: text`; the answer is the
    /// probability-weighted mean index.
    case score(instructions: String, levels: [String])
    /// Yes or no. Optional custom text for each side.
    case noul(instructions: String, falseText: String? = nil, trueText: String? = nil)

    var kind: LayaQuestionKind {
        switch self {
        case .choice: return .choice
        case .score: return .score
        case .noul: return .noul
        }
    }

    var instructions: String {
        switch self {
        case .choice(let instructions, _),
             .score(let instructions, _),
             .noul(let instructions, _, _):
            return instructions
        }
    }

    /// Option texts in label-index order (`render_options` in the Python
    /// runtime). Noul is always `[false, true]`.
    var renderedOptions: [String] {
        switch self {
        case .choice(_, let options):
            return options.map { option in
                guard let description = option.description, !description.isEmpty else {
                    return option.label
                }
                return "\(option.label): \(description)"
            }
        case .score(_, let levels):
            return levels.enumerated().map { "level \($0.offset): \($0.element)" }
        case .noul(_, let falseText, let trueText):
            let no = falseText.flatMap { $0.isEmpty ? nil : $0 } ?? "no, the statement does not hold"
            let yes = trueText.flatMap { $0.isEmpty ? nil : $0 } ?? "yes, the statement holds"
            return ["false: \(no)", "true: \(yes)"]
        }
    }

    /// Number of answer slots the model scores.
    var optionCount: Int { renderedOptions.count }

    /// Rejects questions the Python runtime would also refuse.
    func validate() throws {
        if instructions.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
            throw LayaError.invalidQuestion("Instructions are empty.")
        }
        switch self {
        case .choice(_, let options):
            if options.isEmpty {
                throw LayaError.invalidQuestion("A choice question needs at least one option.")
            }
            var seen = Set<String>()
            for option in options {
                if option.label.isEmpty {
                    throw LayaError.invalidQuestion("Every option needs a label.")
                }
                if !seen.insert(option.label).inserted {
                    throw LayaError.invalidQuestion("Option labels must be unique (\(option.label) repeats).")
                }
            }
        case .score(_, let levels):
            if levels.isEmpty {
                throw LayaError.invalidQuestion("A score question needs at least one level.")
            }
        case .noul:
            break
        }
    }
}

/// Errors raised while preparing input or reading the bundle.
enum LayaError: LocalizedError, Equatable {
    case invalidQuestion(String)
    case tooManyOptions(count: Int, limit: Int)
    case tooManyTokens(count: Int, limit: Int)
    case optionBudgetExceeded
    case bundle(String)
    case model(String)

    var errorDescription: String? {
        switch self {
        case .invalidQuestion(let message):
            return message
        case .tooManyOptions(let count, let limit):
            return "\(count) options, but this export supports at most \(limit)."
        case .tooManyTokens(let count, let limit):
            return "Input has \(count) tokens, but this export supports at most \(limit)."
        case .optionBudgetExceeded:
            return "Too many options for the token budget."
        case .bundle(let message):
            return message
        case .model(let message):
            return message
        }
    }
}
