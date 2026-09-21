import DeviceCheck
import Foundation

/// Orchestrates Sign in with Apple, the one-time App Attest handshake, and later `whoami` assertions.
@MainActor
final class AppAttestController: ObservableObject {
    @Published private(set) var userId: String
    @Published private(set) var deviceId: String
    @Published private(set) var statusMessage: String
    @Published private(set) var statusIsError = false
    @Published private(set) var lastWhoAmI: AppAttestWhoAmI?
    @Published private(set) var isRegistered: Bool
    @Published private(set) var isBusy = false
    @Published private(set) var isSupported: Bool

    var isSignedIn: Bool { !userId.isEmpty }

    private let keys: any AppAttestKeyGenerating
    private let api: AppAttestAPI
    private let store: any AppAttestStoring
    private let appleID: any AppAttestAppleIDChecking

    init(
        keys: any AppAttestKeyGenerating = SystemAppAttestKeys(),
        api: AppAttestAPI = AppAttestAPI(),
        store: (any AppAttestStoring)? = nil,
        appleID: (any AppAttestAppleIDChecking)? = nil
    ) {
        self.keys = keys
        self.api = api
        // Default args are evaluated off the main actor; construct isolated types here.
        let store = store ?? AppAttestUserDefaultsStore()
        self.store = store
        self.appleID = appleID ?? SystemAppAttestAppleID()
        userId = store.userId
        deviceId = store.deviceId
        isRegistered = store.isRegistered
        isSupported = keys.isSupported
        statusMessage = Self.initialStatus(
            supported: keys.isSupported,
            isRegistered: store.isRegistered,
            signedIn: !store.userId.isEmpty
        )
    }

    func applyAppleSignIn(_ result: Result<String, AppAttestAppleSignInError>) async {
        switch result {
        case .success(let appleUserID):
            applyAppleUserID(appleUserID)
            await registerThenWhoami()
        case .failure(.canceled):
            setStatus("Sign in canceled.")
        case .failure(let error):
            setStatus(error.localizedDescription, isError: true)
        }
    }

    func applyAppleUserID(_ appleUserID: String) {
        let trimmed = appleUserID.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            setStatus(AppAttestAppleSignInError.missingUserID.localizedDescription, isError: true)
            return
        }
        if trimmed != store.userId {
            forgetRegistration()
        }
        store.userId = trimmed
        userId = trimmed
        setStatus("Signed in with Apple.")
    }

    func signOut() {
        store.userId = ""
        userId = ""
        store.clearSession()
        isRegistered = false
        lastWhoAmI = nil
        setStatus("Signed out.")
    }

    func refreshAppleIDState() async {
        guard !store.userId.isEmpty else { return }
        switch await appleID.credentialState(forUserID: store.userId) {
        case .revoked, .notFound:
            signOut()
            setStatus("Sign in with Apple was revoked. Sign in again.", isError: true)
        case .authorized, .unknown:
            if isRegistered {
                await whoami()
            } else {
                await registerThenWhoami()
            }
        }
    }

    /// Attest this device, then call `whoami` so the Worker echoes the bound ids.
    func registerThenWhoami() async {
        await register()
        guard isRegistered else { return }
        await whoami()
    }

    func register() async {
        let trimmed = userId.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            setStatus("Sign in with Apple first.", isError: true)
            return
        }
        guard !isBusy else { return }
        isBusy = true
        defer { isBusy = false }

        store.userId = trimmed
        userId = trimmed
        do {
            let challenge = try await api.fetchChallenge()
            let client = AppAttestClientData(
                challenge: challenge.challenge,
                userId: trimmed,
                deviceId: store.deviceId
            )
            let json = try client.jsonBytes()
            let registered: AppAttestRegisterResponse
            if keys.isSupported {
                registered = try await exchangeAttested(json: json)
            } else {
                registered = try await api.registerUnattested(clientDataJSON: json)
            }
            store.keyId = registered.keyId
            store.isRegistered = true
            isRegistered = true
            lastWhoAmI = AppAttestWhoAmI(
                userId: registered.userId,
                deviceId: registered.deviceId,
                keyId: registered.keyId,
                unattested: registered.unattested,
                counter: registered.counter,
                riskMetric: registered.riskMetric
            )
            setStatus(
                registered.unattested
                    ? "Registered an unattested Simulator device."
                    : "Device attested."
            )
        } catch {
            setStatus("Register failed: \(error.localizedDescription)", isError: true)
        }
    }

    func whoami() async {
        guard isRegistered, let keyId = store.keyId, !keyId.isEmpty else {
            setStatus("Register this device first.", isError: true)
            return
        }
        guard !isBusy else { return }
        isBusy = true
        defer { isBusy = false }
        do {
            let challenge = try await api.fetchChallenge()
            let client = AppAttestAssertionClientData(
                action: AppAttestAssertionClientData.whoami,
                challenge: challenge.challenge
            )
            let json = try client.jsonBytes()
            let assertion: Data?
            if keys.isSupported {
                assertion = try await generateAssertion(keyId: keyId, clientDataHash: AppAttestHashing.sha256(json))
            } else {
                assertion = nil
            }
            let result = try await api.whoami(
                keyId: keyId,
                assertionObject: assertion,
                clientDataJSON: json
            )
            lastWhoAmI = result
            setStatus(
                result.unattested
                    ? "Worker accepted the unattested whoami."
                    : "Worker accepted the assertion."
            )
        } catch {
            setStatus("Whoami failed: \(error.localizedDescription)", isError: true)
        }
    }

    private func forgetRegistration() {
        store.isRegistered = false
        store.keyId = nil
        isRegistered = false
        lastWhoAmI = nil
    }

    private func setStatus(_ message: String, isError: Bool = false) {
        statusMessage = message
        statusIsError = isError
    }

    private func exchangeAttested(json: Data) async throws -> AppAttestRegisterResponse {
        let hash = AppAttestHashing.sha256(json)
        let keyId = try await existingOrNewKeyId()
        do {
            let attestation = try await keys.attestKey(keyId, clientDataHash: hash)
            return try await api.register(
                keyId: keyId,
                attestationObject: attestation,
                clientDataJSON: json
            )
        } catch {
            if Self.isInvalidKey(error) {
                store.keyId = nil
                let fresh = try await existingOrNewKeyId()
                let attestation = try await keys.attestKey(fresh, clientDataHash: hash)
                return try await api.register(
                    keyId: fresh,
                    attestationObject: attestation,
                    clientDataJSON: json
                )
            }
            throw error
        }
    }

    private func generateAssertion(keyId: String, clientDataHash: Data) async throws -> Data {
        do {
            return try await keys.generateAssertion(keyId, clientDataHash: clientDataHash)
        } catch {
            if Self.isInvalidKey(error) {
                store.keyId = nil
                store.isRegistered = false
                isRegistered = false
            }
            throw error
        }
    }

    private func existingOrNewKeyId() async throws -> String {
        if let existing = store.keyId, !existing.isEmpty {
            return existing
        }
        let generated = try await keys.generateKey()
        store.keyId = generated
        return generated
    }

    private static func isInvalidKey(_ error: Error) -> Bool {
        let ns = error as NSError
        return ns.domain == DCError.errorDomain && ns.code == DCError.invalidKey.rawValue
    }

    private static func initialStatus(supported: Bool, isRegistered: Bool, signedIn: Bool) -> String {
        if isRegistered {
            return "This device is registered."
        }
        if !signedIn {
            return "Sign in with Apple to attest this device."
        }
        if supported {
            return "Signed in. Attesting this device."
        }
        return "App Attest is unavailable. The handshake uses the Simulator bypass."
    }
}
