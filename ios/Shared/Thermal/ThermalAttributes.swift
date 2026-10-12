import Foundation
import ActivityKit

/// ActivityKit attributes for the thermal-limit Live Activity.
///
/// Fixed attributes are empty. The only live value is the current
/// `ThermalLevel` plus when that level began, so the island can stay an icon
/// and the Lock Screen row can stay one line.
struct ThermalAttributes: ActivityAttributes {
    struct ContentState: Codable, Hashable {
        var level: ThermalLevel
        var changedAt: Date
    }
}
