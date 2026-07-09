import Foundation

/// Pure logic for the Counter experiment: a value clamped to `[minimum, maximum]`.
/// No UI, no framework types — fully unit-testable.
struct CounterModel: Equatable {
    let minimum: Int
    let maximum: Int
    private(set) var value: Int

    init(value: Int = 0, minimum: Int = 0, maximum: Int = 10) {
        precondition(minimum <= maximum, "minimum must be <= maximum")
        self.minimum = minimum
        self.maximum = maximum
        self.value = Self.clamp(value, minimum: minimum, maximum: maximum)
    }

    var canIncrement: Bool { value < maximum }
    var canDecrement: Bool { value > minimum }

    mutating func increment() {
        if canIncrement { value += 1 }
    }

    mutating func decrement() {
        if canDecrement { value -= 1 }
    }

    mutating func reset() {
        value = Self.clamp(0, minimum: minimum, maximum: maximum)
    }

    private static func clamp(_ value: Int, minimum: Int, maximum: Int) -> Int {
        Swift.min(Swift.max(value, minimum), maximum)
    }
}
