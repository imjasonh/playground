import ActivityKit

/// ActivityKit attributes for the thermal Live Activity.
struct ThermalAttributes: ActivityAttributes {
    struct ContentState: Codable, Hashable {
        var level: ThermalLevel
    }
}
