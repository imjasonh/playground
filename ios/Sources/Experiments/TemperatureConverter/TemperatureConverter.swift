import Foundation

/// The two temperature scales the app can convert between.
enum TemperatureScale: CaseIterable, Equatable {
    case celsius
    case fahrenheit

    /// The scale a value is converted *into*.
    var opposite: TemperatureScale {
        switch self {
        case .celsius: return .fahrenheit
        case .fahrenheit: return .celsius
        }
    }

    /// Short unit label for the *source* scale (e.g. "°C").
    var unit: String {
        switch self {
        case .celsius: return "°C"
        case .fahrenheit: return "°F"
        }
    }
}

/// Pure, dependency-free temperature math. Everything here is deterministic and
/// trivially unit-testable — the reason the logic lives outside the views.
enum TemperatureConverter {
    static func celsiusToFahrenheit(_ celsius: Double) -> Double {
        celsius * 9.0 / 5.0 + 32.0
    }

    static func fahrenheitToCelsius(_ fahrenheit: Double) -> Double {
        (fahrenheit - 32.0) * 5.0 / 9.0
    }

    /// Convert `value` interpreted in `scale` to that scale's opposite.
    static func convert(_ value: Double, from scale: TemperatureScale) -> Double {
        switch scale {
        case .celsius: return celsiusToFahrenheit(value)
        case .fahrenheit: return fahrenheitToCelsius(value)
        }
    }
}
