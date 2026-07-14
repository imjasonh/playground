import Foundation
import CoreLocation
#if canImport(WeatherKit)
import WeatherKit
#endif

/// Fetches a WeatherKit current-conditions snapshot for a finished ride.
/// Returns `nil` when there is no usable GPS fix, WeatherKit is unavailable,
/// or the request fails — weather is best-effort and must not block saving.
enum RideWeatherFetcher {
    /// Preferred coordinate: last good track point, else first.
    static func location(for ride: Ride) -> CLLocation? {
        let sample = ride.track.last ?? ride.track.first
        guard let sample else { return nil }
        return CLLocation(latitude: sample.latitude, longitude: sample.longitude)
    }

    static func fetch(for ride: Ride) async -> RideWeather? {
        guard let location = location(for: ride) else { return nil }
        return await fetch(for: location)
    }

    static func fetch(for location: CLLocation) async -> RideWeather? {
        #if canImport(WeatherKit)
        do {
            let weather = try await WeatherService.shared.weather(for: location, including: .current)
            return snapshot(from: weather)
        } catch {
            return nil
        }
        #else
        return nil
        #endif
    }

    #if canImport(WeatherKit)
    /// Maps WeatherKit `CurrentWeather` into our Codable snapshot.
    static func snapshot(from current: CurrentWeather) -> RideWeather {
        RideWeather(
            condition: current.condition.description,
            symbolName: current.symbolName,
            temperatureCelsius: current.temperature.converted(to: .celsius).value,
            apparentTemperatureCelsius: current.apparentTemperature.converted(to: .celsius).value,
            humidity: current.humidity,
            windSpeedMetersPerSecond: current.wind.speed.converted(to: .metersPerSecond).value
        )
    }
    #endif
}
