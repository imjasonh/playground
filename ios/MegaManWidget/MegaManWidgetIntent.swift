import AppIntents
import WidgetKit

/// Widget edit-sheet picker for which Mega Man 2–inspired character to animate.
@available(iOS 17.0, *)
enum MegaManCharacterAppEnum: String, AppEnum {
    case megaMan = "mega-man"
    case metalMan = "metal-man"
    case woodMan = "wood-man"
    case heatMan = "heat-man"
    case flashMan = "flash-man"
    case quickMan = "quick-man"
    case crashMan = "crash-man"
    case bubbleMan = "bubble-man"
    case airMan = "air-man"

    static var typeDisplayRepresentation = TypeDisplayRepresentation(name: "Character")

    static var caseDisplayRepresentations: [MegaManCharacterAppEnum: DisplayRepresentation] = [
        .megaMan: "Mega Man",
        .metalMan: "Metal Man",
        .woodMan: "Wood Man",
        .heatMan: "Heat Man",
        .flashMan: "Flash Man",
        .quickMan: "Quick Man",
        .crashMan: "Crash Man",
        .bubbleMan: "Bubble Man",
        .airMan: "Air Man",
    ]

    var character: MegaManCharacter {
        MegaManCharacter.named(rawValue)
    }
}

@available(iOS 17.0, *)
struct MegaManWidgetIntent: WidgetConfigurationIntent {
    static var title: LocalizedStringResource = "Mega Man 2"
    static var description = IntentDescription(
        "Walk, jump, and shoot loop for Mega Man or a Robot Master."
    )

    @Parameter(title: "Character", default: .megaMan)
    var character: MegaManCharacterAppEnum
}
