import CoreGraphics
import Foundation

/// The Live Translate loop without the camera or the model.
///
/// Each OCR pass goes to `ingest`. `nextBatch` picks the lines to send to the
/// model, `receive` stores translations as the model finishes them, and
/// `finish` closes the batch. `overlays` is what the view draws. The session
/// owns the camera and the model call, and tests drive the same calls with a
/// recorded clip and a fake model.
struct LiveTranslatePipeline {
    /// One model call. Translations for a batch are stored under its language
    /// even when the batch was canceled or the frame that asked for it is gone.
    struct Batch: Equatable {
        let id: Int
        let sources: [String]
        let language: LiveTranslateLanguage
    }

    private(set) var language: LiveTranslateLanguage = .english
    private(set) var overlays: [LiveTranslateOverlay] = []
    /// The batch in flight, if any. One at a time.
    private(set) var batch: Batch?

    private var tracker = LiveTranslateTracker()
    private var memory = LiveTranslateMemory()
    private var pins: [String: LiveTranslatePin] = [:]
    private var backdrops: [String: LiveTranslateBackdrop] = [:]
    private var batchSerial = 0

    var tracks: [LiveTranslateTrack] {
        tracker.tracks
    }

    var isTranslating: Bool {
        batch != nil
    }

    mutating func ingest(_ observations: [LiveTranslateObservation]) {
        tracker.update(with: observations)
        refresh()
    }

    /// Samples the fill color behind each line read this pass. Missed lines keep their last color.
    mutating func sampleBackdrops(_ sample: (CGRect) -> LiveTranslateBackdrop) {
        var next: [String: LiveTranslateBackdrop] = [:]
        for track in tracker.tracks {
            let previous = backdrops[track.id]
            guard track.misses == 0 else {
                next[track.id] = previous
                continue
            }
            let fresh = sample(track.boundingBox)
            next[track.id] = previous?.blended(toward: fresh, weight: 0.5) ?? fresh
        }
        backdrops = next
        refresh()
    }

    /// Starts the next model call, or returns nil while one is in flight or when nothing needs translating.
    mutating func nextBatch(now: Date) -> Batch? {
        guard batch == nil else { return nil }
        let sources = LiveTranslateResultBuilder.translationBatch(
            tracks: tracker.tracks,
            memory: memory,
            language: language,
            now: now
        )
        guard !sources.isEmpty else { return nil }
        batchSerial += 1
        let started = Batch(id: batchSerial, sources: sources, language: language)
        batch = started
        return started
    }

    /// Stores translations the model finished, keyed by index into `batch.sources`.
    mutating func receive(_ translations: [Int: String], for batch: Batch) {
        for (index, translation) in translations where batch.sources.indices.contains(index) {
            memory.remember(source: batch.sources[index], translation: translation, language: batch.language)
        }
        if batch.language == language {
            refresh()
        }
    }

    /// Closes `batch` after storing its last translations. Sources still
    /// without one back off before their next try. Returns false when the
    /// batch was already canceled or replaced.
    @discardableResult
    mutating func finish(_ batch: Batch, translations: [Int: String], now: Date) -> Bool {
        receive(translations, for: batch)
        guard batch.id == self.batch?.id else { return false }
        self.batch = nil
        for source in batch.sources where memory.translation(for: source, language: batch.language) == nil {
            memory.recordFailure(source: source, language: batch.language, at: now)
        }
        return true
    }

    /// Drops the batch in flight. Translations it still delivers go to memory.
    mutating func cancelBatch() {
        batch = nil
    }

    mutating func setLanguage(_ language: LiveTranslateLanguage) {
        guard language != self.language else { return }
        self.language = language
        batch = nil
        refresh()
    }

    /// Forgets line positions after the frame changes shape. Translations stay in memory.
    mutating func clearTracking() {
        tracker.reset()
        pins = [:]
        backdrops = [:]
        overlays = []
    }

    private mutating func refresh() {
        overlays = LiveTranslateResultBuilder.overlays(
            tracks: tracker.tracks,
            memory: memory,
            language: language,
            pins: &pins,
            backdrops: backdrops
        )
    }
}
