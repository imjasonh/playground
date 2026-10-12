import Foundation

/// Whether to start, update, or dismiss the thermal Live Activity.
enum ThermalLiveActivityAction: Equatable {
    case none
    case start(ThermalLevel)
    case update(ThermalLevel)
    case end
}

/// Pure decisions for the thermal Live Activity. No ActivityKit so unit
/// tests can cover the rules without a Live Activity runtime.
enum ThermalLiveActivityPolicy {
    /// How long ActivityKit may keep presenting a last-known level before
    /// marking the Live Activity stale. Dismissal still happens immediately
    /// when the state returns to nominal.
    static let staleAfter: TimeInterval = 10 * 60

    /// Start only when heat is not nominal. End as soon as it is.
    /// Update when the non-nominal level changes.
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
