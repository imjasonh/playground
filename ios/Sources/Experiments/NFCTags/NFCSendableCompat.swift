/// Core NFC session types are not Sendable. The NFC Tags controller hops
/// them from session callbacks onto the main actor. This box makes that hop
/// explicit.
enum NFCIsolation {
    private struct Hop<Value>: @unchecked Sendable {
        let value: Value
    }

    static func hopMain<Value>(
        _ value: Value,
        _ work: @escaping @Sendable @MainActor (Value) -> Void
    ) {
        let hop = Hop(value: value)
        Task { @MainActor in
            work(hop.value)
        }
    }
}
