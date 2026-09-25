import Foundation
@testable import Playground

/// Stands in for the on-device model in Live Translate tests.
///
/// A batch's first line comes back `firstLinePasses` OCR passes after the batch
/// starts, then one more line every `linePasses` passes, the way a streamed
/// reply arrives. Each translation is `EN <source>`.
struct LiveTranslateFakeModel {
    var firstLinePasses = 4
    var linePasses = 1
    private(set) var started: [LiveTranslatePipeline.Batch] = []
    private var inFlight: (batch: LiveTranslatePipeline.Batch, startPass: Int, delivered: Int)?

    static func translation(of source: String) -> String {
        "EN \(source)"
    }

    /// Runs OCR pass `pass` in the session's order: lines the model finished
    /// since the last pass, a follow-up batch if that closed one, the new
    /// readings, then a batch for anything the readings settled.
    mutating func step(pass: Int, observations: [LiveTranslateObservation], pipeline: inout LiveTranslatePipeline) {
        let now = Date(timeIntervalSinceReferenceDate: Double(pass) / 4)
        deliver(at: pass, to: &pipeline, now: now)
        startNext(at: pass, pipeline: &pipeline, now: now)
        pipeline.ingest(observations)
        startNext(at: pass, pipeline: &pipeline, now: now)
    }

    private mutating func startNext(at pass: Int, pipeline: inout LiveTranslatePipeline, now: Date) {
        guard let batch = pipeline.nextBatch(now: now) else { return }
        started.append(batch)
        inFlight = (batch, pass, 0)
    }

    private mutating func deliver(at pass: Int, to pipeline: inout LiveTranslatePipeline, now: Date) {
        guard let flight = inFlight else { return }
        let elapsed = pass - flight.startPass
        guard elapsed >= firstLinePasses else { return }
        let count = flight.batch.sources.count
        let due = min(count, 1 + (elapsed - firstLinePasses) / linePasses)
        var fresh: [Int: String] = [:]
        for index in flight.delivered..<max(flight.delivered, due) {
            fresh[index] = Self.translation(of: flight.batch.sources[index])
        }
        if due == count {
            pipeline.finish(flight.batch, translations: fresh, now: now)
            inFlight = nil
        } else {
            pipeline.receive(fresh, for: flight.batch)
            inFlight = (flight.batch, flight.startPass, due)
        }
    }
}
