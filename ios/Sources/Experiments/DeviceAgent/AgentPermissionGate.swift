import AVFoundation
import Contacts
import CoreLocation
import EventKit
import Foundation
import Speech

/// Requests permissions only when a tool (or voice mode) needs them.
@MainActor
final class AgentPermissionGate: NSObject, ObservableObject {
    static let shared = AgentPermissionGate()

    @Published var prePromptDomain: AgentPermissionDomain?
    @Published var lastDeniedDomain: AgentPermissionDomain?

    private let locationManager = CLLocationManager()
    private var locationContinuation: CheckedContinuation<CLAuthorizationStatus, Never>?

    private override init() {
        super.init()
        locationManager.delegate = self
    }

    func ensure(_ domain: AgentPermissionDomain) async throws {
        switch domain {
        case .microphone:
            try await ensureMicrophone()
        case .speech:
            try await ensureSpeech()
        case .contacts:
            try await ensureContacts()
        case .calendars:
            try await ensureCalendars()
        case .location:
            try await ensureLocation()
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

    private func ensureContacts() async throws {
        let store = CNContactStore()
        let status = CNContactStore.authorizationStatus(for: .contacts)
        if contactsAuthorized(status) {
            return
        }
        switch status {
        case .denied, .restricted:
            lastDeniedDomain = .contacts
            throw AgentToolError.permissionDenied(.contacts)
        case .notDetermined:
            await showPrePrompt(for: .contacts)
            let granted = try await store.requestAccess(for: .contacts)
            prePromptDomain = nil
            if !granted {
                lastDeniedDomain = .contacts
                throw AgentToolError.permissionDenied(.contacts)
            }
        default:
            if contactsAuthorized(status) { return }
            lastDeniedDomain = .contacts
            throw AgentToolError.permissionDenied(.contacts)
        }
    }

    private func contactsAuthorized(_ status: CNAuthorizationStatus) -> Bool {
        if status == .authorized { return true }
        if #available(iOS 18.0, *), status == .limited { return true }
        return false
    }

    private func ensureCalendars() async throws {
        let store = EKEventStore()
        let status = EKEventStore.authorizationStatus(for: .event)
        if calendarsAuthorized(status) {
            return
        }
        switch status {
        case .denied, .restricted:
            lastDeniedDomain = .calendars
            throw AgentToolError.permissionDenied(.calendars)
        case .notDetermined:
            await showPrePrompt(for: .calendars)
            let granted: Bool
            if #available(iOS 17.0, *) {
                granted = try await store.requestFullAccessToEvents()
            } else {
                granted = try await withCheckedThrowingContinuation { cont in
                    store.requestAccess(to: .event) { ok, error in
                        if let error {
                            cont.resume(throwing: error)
                        } else {
                            cont.resume(returning: ok)
                        }
                    }
                }
            }
            prePromptDomain = nil
            if !granted {
                lastDeniedDomain = .calendars
                throw AgentToolError.permissionDenied(.calendars)
            }
        default:
            if calendarsAuthorized(status) { return }
            lastDeniedDomain = .calendars
            throw AgentToolError.permissionDenied(.calendars)
        }
    }

    private func calendarsAuthorized(_ status: EKAuthorizationStatus) -> Bool {
        if status == .authorized { return true }
        if #available(iOS 17.0, *) {
            return status == .fullAccess || status == .writeOnly
        }
        return false
    }

    private func ensureLocation() async throws {
        let status = locationManager.authorizationStatus
        switch status {
        case .authorizedAlways, .authorizedWhenInUse:
            return
        case .denied, .restricted:
            lastDeniedDomain = .location
            throw AgentToolError.permissionDenied(.location)
        case .notDetermined:
            await showPrePrompt(for: .location)
            let newStatus = await withCheckedContinuation { (cont: CheckedContinuation<CLAuthorizationStatus, Never>) in
                locationContinuation = cont
                locationManager.requestWhenInUseAuthorization()
            }
            prePromptDomain = nil
            switch newStatus {
            case .authorizedAlways, .authorizedWhenInUse:
                return
            default:
                lastDeniedDomain = .location
                throw AgentToolError.permissionDenied(.location)
            }
        @unknown default:
            throw AgentToolError.unavailable("Unknown location permission state.")
        }
    }

    private func showPrePrompt(for domain: AgentPermissionDomain) async {
        prePromptDomain = domain
        try? await Task.sleep(nanoseconds: 350_000_000)
    }
}

extension AgentPermissionGate: CLLocationManagerDelegate {
    nonisolated func locationManagerDidChangeAuthorization(_ manager: CLLocationManager) {
        Task { @MainActor in
            guard let cont = locationContinuation else { return }
            // Ignore the initial callback before we request.
            if manager.authorizationStatus == .notDetermined { return }
            locationContinuation = nil
            cont.resume(returning: manager.authorizationStatus)
        }
    }
}
