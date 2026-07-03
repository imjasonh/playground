import Foundation

/// View model backing `ContentView`. Holds the user's input and the selected
/// source scale, and derives display strings. Marked `@MainActor` because it
/// drives SwiftUI state; the derivation logic is still synchronous and testable.
@MainActor
final class ConverterViewModel: ObservableObject {
    @Published var inputText: String = ""
    @Published var scale: TemperatureScale = .celsius

    /// Placeholder shown when the input is empty or not a number.
    static let placeholder = "—"

    /// The numeric value parsed from `inputText`, or `nil` when it isn't a
    /// finite number. Accepts surrounding whitespace.
    var parsedValue: Double? {
        let trimmed = inputText.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty, let value = Double(trimmed), value.isFinite else {
            return nil
        }
        return value
    }

    /// Formatted converted temperature, or the placeholder for invalid input.
    var convertedText: String {
        guard let value = parsedValue else { return Self.placeholder }
        return Self.format(TemperatureConverter.convert(value, from: scale))
    }

    /// Unit label for the *result* (the scale we convert into).
    var resultUnit: String {
        scale.opposite.unit
    }

    /// Unit label for the *input* (the scale we convert from).
    var inputUnit: String {
        scale.unit
    }

    func toggleScale() {
        scale = scale.opposite
    }

    /// Round to one decimal place, normalizing "-0.0" to "0.0".
    static func format(_ value: Double) -> String {
        let rounded = (value * 10).rounded() / 10
        let normalized = rounded == 0 ? 0 : rounded
        return String(format: "%.1f", normalized)
    }
}
