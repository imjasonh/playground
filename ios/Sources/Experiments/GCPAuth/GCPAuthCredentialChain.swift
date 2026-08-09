import Foundation

/// The three exchanges that turn "a genuine install of this app, driven by this
/// signed-in user" into a short-lived Google access token:
///
/// 1. **App Attest → App Check.** The Secure Enclave proves the app is real.
/// 2. **App Check → Firebase Auth.** The user signs in; enforcement rejects
///    sign-ins that didn't come from an attested install.
/// 3. **Firebase ID token → STS.** Workload Identity Federation trades it for a
///    Google access token that expires in an hour.
///
/// Each step is a plain `async` function so the UI can run them one at a time
/// and show its work, and so tests can drive the whole thing over a fake
/// transport.
struct GCPAuthCredentialChain {
    let configuration: GCPAuthConfiguration
    let attestor: GCPAuthAttestor
    let store: GCPAuthStateStore
    let appCheck: GCPAuthAppCheckClient
    let firebase: GCPAuthFirebaseAuthClient
    let workloadIdentity: GCPAuthWorkloadIdentityClient

    // MARK: - Step 1: prove the app is genuine

    func appCheckToken() async throws -> GCPAuthToken {
        if let keyID = store.appAttestKeyID, let artifact = store.appCheckArtifact {
            do {
                return try await assertExistingKey(keyID: keyID, artifact: artifact)
            } catch let error as GCPAuthError {
                // A key can stop resolving for ordinary reasons — restore onto new
                // hardware, a reinstall, an artifact Firebase has rotated past.
                // Attesting a fresh key is the documented recovery, so do it once
                // instead of stranding the install; anything that isn't the server
                // rejecting us still propagates.
                guard case .http(let status, _) = error, (400..<500).contains(status) else {
                    throw error
                }
                store.reset()
            }
        }
        return try await attestNewKey()
    }

    private func attestNewKey() async throws -> GCPAuthToken {
        // Reuse a key id that was generated but never finished attesting — App
        // Attest rate-limits key creation, so burning a fresh one on every retry
        // is how an install ends up locked out of its own backend.
        let keyID: String
        if let existing = store.appAttestKeyID {
            keyID = existing
        } else {
            keyID = try await attestor.generateKey()
            store.appAttestKeyID = keyID
        }

        let challenge = try await appCheck.generateChallenge()
        let attestation = try await attestor.attestKey(
            keyID,
            clientDataHash: GCPAuthClientData.attestationHash(challenge: challenge)
        )
        let exchanged = try await appCheck.exchangeAttestation(
            keyID: keyID,
            attestation: attestation,
            challenge: challenge
        )
        store.appCheckArtifact = exchanged.artifact
        return exchanged.token
    }

    private func assertExistingKey(keyID: String, artifact: Data) async throws -> GCPAuthToken {
        let challenge = try await appCheck.generateChallenge()
        let assertion = try await attestor.generateAssertion(
            keyID,
            clientDataHash: GCPAuthClientData.assertionHash(artifact: artifact, challenge: challenge)
        )
        return try await appCheck.exchangeAssertion(
            artifact: artifact,
            assertion: assertion,
            challenge: challenge
        )
    }

    // MARK: - Step 2: identify the user

    func signIn(appCheckToken: String?) async throws -> GCPAuthIdentity {
        guard configuration.appleSignInEnabled else {
            return try await firebase.signInAnonymously(appCheckToken: appCheckToken)
        }
        let apple = try await GCPAuthAppleSignInController().signIn()
        return try await firebase.signInWithApple(
            identityToken: apple.identityToken,
            rawNonce: apple.rawNonce,
            appCheckToken: appCheckToken
        )
    }

    // MARK: - Step 3: federate into Google

    func googleAccessToken(firebaseIDToken: String) async throws -> GCPAuthToken {
        let federated = try await workloadIdentity.federate(firebaseIDToken: firebaseIDToken)
        guard !configuration.serviceAccountEmail.isEmpty else { return federated }
        return try await workloadIdentity.impersonate(
            serviceAccountEmail: configuration.serviceAccountEmail,
            federatedToken: federated.value
        )
    }
}

extension GCPAuthCredentialChain {
    /// Builds the chain the app actually uses.
    ///
    /// Without a configured project it wires up an in-process transport and a
    /// stub attestor so the experiment demonstrates the flow offline; with one,
    /// it talks to the real endpoints from the Secure Enclave.
    static func make(
        configuration: GCPAuthConfiguration,
        store: GCPAuthStateStore,
        simulatedLatency: TimeInterval = 0
    ) -> GCPAuthCredentialChain {
        let live = configuration.isConfigured
        let attestor: GCPAuthAttestor = live && GCPAuthDeviceCheckAttestor().isSupported
            ? GCPAuthDeviceCheckAttestor()
            : GCPAuthSimulatedAttestor()
        let transport: GCPAuthTransport = live
            ? GCPAuthURLSessionTransport()
            : GCPAuthSimulatedTransport(configuration: configuration, latency: simulatedLatency)
        return make(configuration: configuration, store: store, attestor: attestor, transport: transport)
    }

    static func make(
        configuration: GCPAuthConfiguration,
        store: GCPAuthStateStore,
        attestor: GCPAuthAttestor,
        transport: GCPAuthTransport
    ) -> GCPAuthCredentialChain {
        let http = GCPAuthHTTPClient(transport: transport)
        return GCPAuthCredentialChain(
            configuration: configuration,
            attestor: attestor,
            store: store,
            appCheck: GCPAuthAppCheckClient(configuration: configuration, http: http),
            firebase: GCPAuthFirebaseAuthClient(configuration: configuration, http: http),
            workloadIdentity: GCPAuthWorkloadIdentityClient(configuration: configuration, http: http)
        )
    }
}
