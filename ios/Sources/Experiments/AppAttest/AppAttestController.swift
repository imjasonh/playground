import DeviceCheck
import Foundation

/// Orchestrates Sign in with Apple, the one-time App Attest handshake, and later `whoami` calls.
@MainActor
final class AppAttestController: ObservableObject {
    @Published private(set) var userId: String
    @Published private(set) var deviceId: String
    @Published private(set) var statusMessage: String
    @Published private(set) var statusIsError = false
    @Published private(set) var lastWhoAmI: AppAttestWhoAmI?
    @Published private(set) var hasToken: Bool
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
        hasToken = store.token != nil
        isSupported = keys.isSupported
        statusMessage = Self.initialStatus(
            supported: keys.isSupported,
            hasToken: store.token != nil,
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
            forgetStoredToken()
        }
        store.userId = trimmed
        userId = trimmed
        setStatus("Signed in with Apple.")
    }

    func signOut() {
        store.userId = ""
        userId = ""
        forgetStoredToken()
        setStatus("Signed out.")
    }

    func refreshAppleIDState() async {
        guard !store.userId.isEmpty else { return }
        switch await appleID.credentialState(forUserID: store.userId) {
        case .revoked, .notFound:
            signOut()
            setStatus("Sign in with Apple was revoked. Sign in again.", isError: true)
        case .authorized, .unknown:
            if hasToken {
                await whoami()
            } else {
                await registerThenWhoami()
            }
        }
    }

    /// Attest this device, then call `whoami` so the Worker echoes the bound ids.
    func registerThenWhoami() async {
        await register()
        guard hasToken else { return }
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
            let token: AppAttestTokenResponse
            if keys.isSupported {
                token = try await exchangeAttested(json: json)
            } else {
                token = try await api.exchangeUnattestedToken(clientDataJSON: json)
            }
            store.token = token.token
            hasToken = true
            lastWhoAmI = AppAttestWhoAmI(
                userId: token.userId,
                deviceId: token.deviceId,
                keyId: token.keyId,
                unattested: token.unattested
            )
            setStatus(
                token.unattested
                    ? "Issued an unattested token for the Simulator."
                    : "Device attested. Token stored."
            )
        } catch {
            setStatus("Register failed: \(error.localizedDescription)", isError: true)
        }
    }

    func whoami() async {
        guard let token = store.token else {
            setStatus("Register this device first.", isError: true)
            return
        }
        guard !isBusy else { return }
        isBusy = true
        defer { isBusy = false }
        do {
            let result = try await api.whoami(token: token)
            lastWhoAmI = result
            setStatus(
                result.unattested
                    ? "Worker accepted the unattested token."
                    : "Worker accepted the attested token."
            )
        } catch {
            setStatus("Call whoami failed: \(error.localizedDescription)", isError: true)
        }
    }

    func forgetToken() {
        store.clearSession()
        hasToken = false
        lastWhoAmI = nil
        setStatus("Forgot the stored token and App Attest key id.")
    }

    private func forgetStoredToken() {
        store.token = nil
        hasToken = false
        lastWhoAmI = nil
    }

    private func setStatus(_ message: String, isError: Bool = false) {
        statusMessage = message
        statusIsError = isError
    }

    private func exchangeAttested(json: Data) async throws -> AppAttestTokenResponse {
        let hash = AppAttestHashing.sha256(json)
        let keyId = try await existingOrNewKeyId()
        do {
            let attestation = try await keys.attestKey(keyId, clientDataHash: hash)
            return try await api.exchangeToken(
                keyId: keyId,
                attestationObject: attestation,
                clientDataJSON: json
            )
        } catch {
            if Self.isInvalidKey(error) {
                store.keyId = nil
                let fresh = try await existingOrNewKeyId()
                let attestation = try await keys.attestKey(fresh, clientDataHash: hash)
                return try await api.exchangeToken(
                    keyId: fresh,
                    attestationObject: attestation,
                    clientDataJSON: json
                )
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

    private static func initialStatus(supported: Bool, hasToken: Bool, signedIn: Bool) -> String {
        if hasToken {
            return "A token is stored on this device."
        }
        if !signedIn {
            return "Sign in with Apple to attest this device."
        }
        if supported {
            return "Signed in. Attesting this device."
        }
        return "App Attest is unavailable. Register uses the Simulator bypass."
    }
}
