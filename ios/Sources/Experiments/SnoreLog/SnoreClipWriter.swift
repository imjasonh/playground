import AVFoundation
import Foundation

/// Writes mono float PCM to a CAF file for later playback / analysis.
enum SnoreClipWriter {
    static func write(
        samples: [Float],
        sampleRate: Double,
        to url: URL
    ) throws {
        guard !samples.isEmpty else {
            throw ClipError.empty
        }
        guard let format = AVAudioFormat(commonFormat: .pcmFormatFloat32, sampleRate: sampleRate, channels: 1, interleaved: false) else {
            throw ClipError.badFormat
        }

        let directory = url.deletingLastPathComponent()
        try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
        if FileManager.default.fileExists(atPath: url.path) {
            try FileManager.default.removeItem(at: url)
        }

        let file = try AVAudioFile(forWriting: url, settings: format.settings)
        let frameCount = AVAudioFrameCount(samples.count)
        guard let buffer = AVAudioPCMBuffer(pcmFormat: format, frameCapacity: frameCount) else {
            throw ClipError.badFormat
        }
        buffer.frameLength = frameCount
        if let channel = buffer.floatChannelData?[0] {
            samples.withUnsafeBufferPointer { src in
                channel.update(from: src.baseAddress!, count: samples.count)
            }
        }
        try file.write(from: buffer)
    }

    enum ClipError: Error {
        case empty
        case badFormat
    }
}
