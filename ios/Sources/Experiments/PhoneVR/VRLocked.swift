import Foundation

/// A value guarded by a lock, for state that crosses between the render
/// thread, sensor queues, and the main thread.
final class VRLocked<Value>: @unchecked Sendable {
    private let lock = NSLock()
    private var value: Value

    init(_ value: Value) {
        self.value = value
    }

    func withLock<Result>(_ body: (inout Value) throws -> Result) rethrows -> Result {
        lock.lock()
        defer { lock.unlock() }
        return try body(&value)
    }

    func get() -> Value {
        withLock { $0 }
    }

    func set(_ newValue: Value) {
        withLock { $0 = newValue }
    }
}
