import AVFoundation

enum AudioTapBufferSizing {
    /// iOS 27 audio taps require requested buffers between 100 and 400 ms.
    static let durationSeconds = 0.1
    private static let fallbackSampleRate = 48_000.0

    static func frameCount(sampleRate: Double) -> AVAudioFrameCount {
        let rate = sampleRate.isFinite && sampleRate > 0 ? sampleRate : fallbackSampleRate
        let frames = (rate * durationSeconds).rounded(.up)
        return AVAudioFrameCount(min(frames, Double(UInt32.max)))
    }
}
