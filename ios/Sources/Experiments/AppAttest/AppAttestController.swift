import DeviceCheck
import Foundation

/// Orchestrates the one-time App Attest handshake and later `whoami` calls.
@MainActor
final class AppAttestController: ObservableObject {
    @Published var userId: String
    @Published private(set) var deviceId: String
    @Published private(set) var statusMessage: String
    @Published private(set) var lastWhoAmI: AppAttestWhoAmI?
    @Published private(set) var hasToken: Bool
    @Published private(set) var isBusy = false
    @Published private(set) var isSupported: Bool

    private let keys: any AppAttestKeyGenerating
    private let api: AppAttestAPI
    private let store: any AppAttestStoring

    init(
        keys: any AppAttestKeyGenerating = SystemAppAttestKeys(),
        api: AppAttestAPI = AppAttestAPI(),
        store: any AppAttestStoring = AppAttestUserDefaultsStore()
    ) {
        self.keys = keys
        self.api = api
        self.store = store
        userId = store.userId
        deviceId = store.deviceId
        hasToken = store.token != nil
        isSupported = keys.isSupported
        statusMessage = Self.initialStatus(
            supported: keys.isSupported,
            hasToken: store.token != nil
        )
    }

    func register() async {
        let trimmed = userId.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            statusMessage = "Enter a user id."
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
            statusMessage = token.unattested
                ? "Issued an unattested token for the Simulator."
                : "Device attested. Token stored."
        } catch {
            statusMessage = error.localizedDescription
        }
    }

    func whoami() async {
        guard let token = store.token else {
            statusMessage = "Register this device first."
            return
        }
        guard !isBusy else { return }
        isBusy = true
        defer { isBusy = false }
        do {
            let result = try await api.whoami(token: token)
            lastWhoAmI = result
            statusMessage = result.unattested
                ? "Worker accepted the unattested token."
                : "Worker accepted the attested token."
        } catch {
            statusMessage = error.localizedDescription
        }
    }

    func forgetToken() {
        store.clearSession()
        hasToken = false
        lastWhoAmI = nil
        statusMessage = "Forgot the stored token and App Attest key id."
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

    private static func initialStatus(supported: Bool, hasToken: Bool) -> String {
        if hasToken {
            return "A token is stored on this device."
        }
        if supported {
            return "Register to attest this device and mint a token."
        }
        return "App Attest is unavailable. Register uses the Simulator bypass."
    }
}
