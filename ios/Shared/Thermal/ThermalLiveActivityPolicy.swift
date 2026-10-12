import Foundation

enum ThermalLiveActivityAction: Equatable {
    case none
    case start(ThermalLevel)
    case update(ThermalLevel)
    case end
}

/// Live Activity start, update, and end rules. No ActivityKit, so tests can
/// cover them without a Live Activity runtime.
enum ThermalLiveActivityPolicy {
    /// ActivityKit marks the last-known level stale after this interval.
    /// Dismissal is still immediate when the state returns to nominal.
    static let staleAfter: TimeInterval = 10 * 60

    static func action(presented: ThermalLevel?, incoming: ThermalLevel) -> ThermalLiveActivityAction {
        if !incoming.showsLiveActivity {
            return presented == nil ? .none : .end
        }
        guard let presented else { return .start(incoming) }
        if presented == incoming { return .none }
        return .update(incoming)
    }

    static func staleDate(from now: Date = Date()) -> Date {
        now.addingTimeInterval(staleAfter)
    }
}
