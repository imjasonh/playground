import Foundation

/// One logged snore (or loudness) event from a sleep session.
struct SnoreEvent: Identifiable, Codable, Equatable {
    let id: UUID
    /// Wall-clock time the event started.
    let startedAt: Date
    /// Session-relative seconds from session start.
    let sessionOffset: TimeInterval
    let durationSeconds: TimeInterval
    /// Peak RMS (0…~1) observed during the event.
    let peakRMS: Double
    let noiseFloorAtOnset: Double
    /// Relative filename under the session's clips directory, e.g. "clip-<uuid>.caf".
    let clipFileName: String

    init(
        id: UUID = UUID(),
        startedAt: Date,
        sessionOffset: TimeInterval,
        durationSeconds: TimeInterval,
        peakRMS: Double,
        noiseFloorAtOnset: Double,
        clipFileName: String
    ) {
        self.id = id
        self.startedAt = startedAt
        self.sessionOffset = sessionOffset
        self.durationSeconds = durationSeconds
        self.peakRMS = peakRMS
        self.noiseFloorAtOnset = noiseFloorAtOnset
        self.clipFileName = clipFileName
    }
}

/// A full night (or nap) monitoring session with its snore events.
struct SleepSession: Identifiable, Codable, Equatable {
    let id: UUID
    let startedAt: Date
    var endedAt: Date?
    var durationSeconds: TimeInterval
    var events: [SnoreEvent]
    var snoreCount: Int

    init(
        id: UUID = UUID(),
        startedAt: Date = Date(),
        endedAt: Date? = nil,
        durationSeconds: TimeInterval = 0,
        events: [SnoreEvent] = []
    ) {
        self.id = id
        self.startedAt = startedAt
        self.endedAt = endedAt
        self.durationSeconds = durationSeconds
        self.events = events
        self.snoreCount = events.count
    }
}
