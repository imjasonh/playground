import Foundation

/// Fixed-capacity circular buffer of mono float samples.
///
/// Holds a few seconds of recent audio in RAM so a snore event can be saved
/// with pre-roll without writing overnight audio to disk.
struct SnoreRingBuffer {
    private var samples: [Float]
    private var writeIndex = 0
    private(set) var count = 0

    let capacity: Int

    init(capacity: Int) {
        precondition(capacity > 0)
        self.capacity = capacity
        self.samples = Array(repeating: 0, count: capacity)
    }

    mutating func append(_ chunk: UnsafeBufferPointer<Float>) {
        for sample in chunk {
            samples[writeIndex] = sample
            writeIndex = (writeIndex + 1) % capacity
            if count < capacity { count += 1 }
        }
    }

    mutating func append(_ chunk: [Float]) {
        chunk.withUnsafeBufferPointer { append($0) }
    }

    /// Returns the most recent `requested` samples (or fewer if not yet full),
    /// oldest-first.
    func recentSamples(_ requested: Int) -> [Float] {
        let n = min(requested, count)
        guard n > 0 else { return [] }
        var result = [Float](repeating: 0, count: n)
        let start = (writeIndex - n + capacity) % capacity
        for i in 0..<n {
            result[i] = samples[(start + i) % capacity]
        }
        return result
    }

    mutating func reset() {
        writeIndex = 0
        count = 0
        for i in 0..<capacity { samples[i] = 0 }
    }
}
