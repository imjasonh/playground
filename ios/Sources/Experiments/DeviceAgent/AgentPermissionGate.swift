import AVFoundation
import Foundation
import Speech

/// Requests mic / speech permissions only when voice mode needs them.
@MainActor
final class AgentPermissionGate: NSObject, ObservableObject {
    static let shared = AgentPermissionGate()

    @Published var prePromptDomain: AgentPermissionDomain?
    @Published var lastDeniedDomain: AgentPermissionDomain?

    private override init() {
        super.init()
    }

    func ensure(_ domain: AgentPermissionDomain) async throws {
        switch domain {
        case .microphone:
            try await ensureMicrophone()
        case .speech:
            try await ensureSpeech()
        }
    }

    private func ensureMicrophone() async throws {
        switch AVAudioSession.sharedInstance().recordPermission {
        case .granted:
            return
        case .denied:
            lastDeniedDomain = .microphone
            throw AgentToolError.permissionDenied(.microphone)
        case .undetermined:
            await showPrePrompt(for: .microphone)
            let granted = await withCheckedContinuation { (cont: CheckedContinuation<Bool, Never>) in
                AVAudioSession.sharedInstance().requestRecordPermission { cont.resume(returning: $0) }
            }
            prePromptDomain = nil
            if !granted {
                lastDeniedDomain = .microphone
                throw AgentToolError.permissionDenied(.microphone)
            }
        @unknown default:
            throw AgentToolError.unavailable("Unknown microphone permission state.")
        }
    }

    private func ensureSpeech() async throws {
        switch SFSpeechRecognizer.authorizationStatus() {
        case .authorized:
            return
        case .denied, .restricted:
            lastDeniedDomain = .speech
            throw AgentToolError.permissionDenied(.speech)
        case .notDetermined:
            await showPrePrompt(for: .speech)
            let newStatus = await withCheckedContinuation { (cont: CheckedContinuation<SFSpeechRecognizerAuthorizationStatus, Never>) in
                SFSpeechRecognizer.requestAuthorization { cont.resume(returning: $0) }
            }
            prePromptDomain = nil
            guard newStatus == .authorized else {
                lastDeniedDomain = .speech
                throw AgentToolError.permissionDenied(.speech)
            }
        @unknown default:
            throw AgentToolError.unavailable("Unknown speech permission state.")
        }
    }

    private func showPrePrompt(for domain: AgentPermissionDomain) async {
        prePromptDomain = domain
        try? await Task.sleep(nanoseconds: 350_000_000)
    }
}
