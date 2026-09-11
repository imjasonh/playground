import AVFoundation
import Foundation
import Speech

/// Hold-to-talk / tap-to-toggle speech → text for Device Agent prompts.
@MainActor
final class AgentVoiceCapture: ObservableObject {
    @Published var isRecording = false
    @Published var transcript = ""
    @Published var statusMessage = "Voice idle"
    @Published var lastError: String?

    private let permissions = AgentPermissionGate.shared
    private let audioEngine = AVAudioEngine()
    private var recognizer: SFSpeechRecognizer?
    private var request: SFSpeechAudioBufferRecognitionRequest?
    private var task: SFSpeechRecognitionTask?

    func toggle() async {
        if isRecording {
            stop()
            return
        }
        await start()
    }

    func start() async {
        lastError = nil
        do {
            try await permissions.ensure(.microphone)
            try await permissions.ensure(.speech)
        } catch {
            lastError = error.localizedDescription
            statusMessage = error.localizedDescription
            return
        }

        recognizer = SFSpeechRecognizer(locale: Locale(identifier: "en-US"))
        guard let recognizer, recognizer.isAvailable else {
            statusMessage = "Speech recognizer unavailable for this locale."
            return
        }

        let session = AVAudioSession.sharedInstance()
        do {
            try session.setCategory(.record, mode: .measurement, options: .duckOthers)
            try session.setActive(true, options: .notifyOthersOnDeactivation)
        } catch {
            lastError = error.localizedDescription
            statusMessage = "Could not activate audio session."
            return
        }

        let request = SFSpeechAudioBufferRecognitionRequest()
        request.shouldReportPartialResults = true
        if recognizer.supportsOnDeviceRecognition {
            request.requiresOnDeviceRecognition = true
        }
        self.request = request

        let input = audioEngine.inputNode
        let format = input.outputFormat(forBus: 0)
        input.removeTap(onBus: 0)
        let sink = SpeechRequestAudioSink(request: request)
        do {
            try input.installAudioTap(
                onBus: 0,
                bufferSize: AudioTapBufferSizing.frameCount(sampleRate: format.sampleRate),
                format: format
            ) { buffer, _ in
                sink.append(buffer)
            }
        } catch {
            lastError = error.localizedDescription
            statusMessage = "Could not monitor microphone input."
            return
        }

        audioEngine.prepare()
        do {
            try audioEngine.start()
        } catch {
            lastError = error.localizedDescription
            statusMessage = "Could not start microphone."
            input.removeTap(onBus: 0)
            return
        }

        isRecording = true
        statusMessage = "Listening…"
        task = recognizer.recognitionTask(with: request) { [weak self] result, error in
            Task { @MainActor in
                guard let self else { return }
                if let result {
                    self.transcript = result.bestTranscription.formattedString
                    if result.isFinal {
                        self.statusMessage = "Voice ready. Edit or send"
                        self.stopEngineOnly()
                    }
                }
                if let error {
                    self.lastError = error.localizedDescription
                    self.statusMessage = error.localizedDescription
                    self.stop()
                }
            }
        }
    }

    func stop() {
        stopEngineOnly()
        request?.endAudio()
        task?.cancel()
        task = nil
        request = nil
        isRecording = false
        if !transcript.isEmpty {
            statusMessage = "Voice ready. Edit or send"
        } else if lastError == nil {
            statusMessage = "Voice idle"
        }
    }

    private func stopEngineOnly() {
        if audioEngine.isRunning {
            audioEngine.stop()
        }
        audioEngine.inputNode.removeTap(onBus: 0)
        try? AVAudioSession.sharedInstance().setActive(false, options: .notifyOthersOnDeactivation)
        isRecording = false
    }
}

/// `SFSpeechAudioBufferRecognitionRequest` is not `Sendable`, but the audio tap
/// invokes this sink serially and this is its only writer.
private final class SpeechRequestAudioSink: @unchecked Sendable {
    private let request: SFSpeechAudioBufferRecognitionRequest

    init(request: SFSpeechAudioBufferRecognitionRequest) {
        self.request = request
    }

    func append(_ buffer: AVReadOnlyAudioPCMBuffer) {
        let copy: AVAudioPCMBuffer? = AVAudioPCMBuffer(copying: buffer)
        if let copy {
            request.append(copy)
        }
    }
}
