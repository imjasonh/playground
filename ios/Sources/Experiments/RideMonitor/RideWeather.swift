import Foundation

/// Compact weather snapshot captured when a ride ends (WeatherKit current
/// conditions at a track coordinate). Optional on `Ride` so older saved JSON
/// still decodes.
struct RideWeather: Codable, Equatable {
    /// Human-readable condition from WeatherKit (e.g. "Partly Cloudy").
    let condition: String
    /// SF Symbol name WeatherKit recommends for this condition.
    let symbolName: String
    /// Temperature in Celsius (locale formatting happens at display time).
    let temperatureCelsius: Double
    /// Feels-like temperature in Celsius, when available.
    let apparentTemperatureCelsius: Double?
    /// Relative humidity in 0...1.
    let humidity: Double?
    /// Wind speed in meters per second.
    let windSpeedMetersPerSecond: Double?

    /// Short line for list/detail UI, e.g. "Partly Cloudy · 62°".
    var displayLine: String {
        let temp = Measurement(value: temperatureCelsius, unit: UnitTemperature.celsius)
        let formatted = temp.formatted(
            .measurement(width: .narrow, usage: .weather, numberFormatStyle: .number.precision(.fractionLength(0)))
        )
        return "\(condition) · \(formatted)"
    }

    /// Compact facts line for the on-device summary model.
    var factsLine: String {
        var parts: [String] = [
            condition,
            String(format: "%.0f°C", temperatureCelsius),
        ]
        if let humidity {
            parts.append(String(format: "humidity %.0f%%", humidity * 100))
        }
        if let windSpeedMetersPerSecond {
            let mph = windSpeedMetersPerSecond * 2.236936
            parts.append(String(format: "wind %.0f mph", mph))
        }
        return parts.joined(separator: ", ")
    }
}
