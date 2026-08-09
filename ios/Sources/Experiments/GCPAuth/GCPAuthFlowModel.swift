import Foundation

enum GCPAuthStep: String, CaseIterable, Identifiable, Hashable {
    case appCheck = "app-check"
    case signIn = "sign-in"
    case federate = "federate"

    var id: String { rawValue }

    var title: String {
        switch self {
        case .appCheck: return "Attest the app"
        case .signIn: return "Identify the user"
        case .federate: return "Federate into Google"
        }
    }

    var detail: String {
        switch self {
        case .appCheck:
            return "Secure Enclave key → App Attest → Firebase App Check token."
        case .signIn:
            return "Firebase Auth sign-in, carrying the App Check token so enforcement can turn away unattested installs."
        case .federate:
            return "Workload Identity Federation trades the Firebase ID token for a short-lived Google access token."
        }
    }
}

enum GCPAuthStepState: Equatable {
    case pending
    case running
    case succeeded(String)
    case failed(String)

    var symbolName: String {
        switch self {
        case .pending: return "circle.dashed"
        case .running: return "clock"
        case .succeeded: return "checkmark.circle.fill"
        case .failed: return "xmark.octagon.fill"
        }
    }
}

/// Drives the credential chain one step at a time and publishes what happened,
/// so the experiment shows the exchanges instead of only their result.
final class GCPAuthFlowModel: ObservableObject {
    @Published private(set) var states: [GCPAuthStep: GCPAuthStepState] = GCPAuthFlowModel.pendingStates
    @Published private(set) var tokens: [GCPAuthStep: GCPAuthToken] = [:]
    @Published private(set) var isRunning = false
    @Published private(set) var statusMessage: String
    @Published private(set) var identity: GCPAuthIdentity?

    let configuration: GCPAuthConfiguration
    private let store: GCPAuthStateStore
    private let chain: GCPAuthCredentialChain

    static let pendingStates: [GCPAuthStep: GCPAuthStepState] = Dictionary(
        uniqueKeysWithValues: GCPAuthStep.allCases.map { ($0, GCPAuthStepState.pending) }
    )

    /// True when nothing here touches the network or the Secure Enclave.
    var isSimulated: Bool { !configuration.isConfigured }

    init(configuration: GCPAuthConfiguration, store: GCPAuthStateStore, chain: GCPAuthCredentialChain) {
        self.configuration = configuration
        self.store = store
        self.chain = chain
        self.statusMessage = configuration.isConfigured
            ? "Ready — live against project \(configuration.projectID)."
            : "Simulated: no project is configured, so the exchanges are answered in-process."
    }

    convenience init() {
        let configuration = GCPAuthConfiguration.fromBundle()
        // Only reach for the Keychain when there is real App Attest state worth
        // keeping. The simulated path has nothing worth persisting.
        let store: GCPAuthStateStore = configuration.isConfigured
            ? GCPAuthKeychainStore()
            : GCPAuthInMemoryStore()
        self.init(
            configuration: configuration,
            store: store,
            chain: .make(configuration: configuration, store: store, simulatedLatency: 0.35)
        )
    }

    @MainActor
    func run() async {
        guard !isRunning else { return }
        isRunning = true
        states = Self.pendingStates
        tokens.removeAll()
        identity = nil
        defer { isRunning = false }

        let chain = self.chain
        do {
            let appCheckToken = try await perform(.appCheck) {
                try await chain.appCheckToken()
            }
            tokens[.appCheck] = appCheckToken
            set(.appCheck, .succeeded("App Check token \(appCheckToken.redacted)"))

            let signedIn = try await perform(.signIn) {
                try await chain.signIn(appCheckToken: appCheckToken.value)
            }
            identity = signedIn
            tokens[.signIn] = signedIn.idToken
            set(.signIn, .succeeded("\(signedIn.provider.label) · uid \(signedIn.userID)"))

            let accessToken = try await perform(.federate) {
                try await chain.googleAccessToken(firebaseIDToken: signedIn.idToken.value)
            }
            tokens[.federate] = accessToken
            let hop = configuration.serviceAccountEmail.isEmpty
                ? "federated principal"
                : "impersonating \(configuration.serviceAccountEmail)"
            set(.federate, .succeeded("Google access token (\(hop)) \(accessToken.redacted)"))

            statusMessage = isSimulated
                ? "Chain complete — simulated. Every token here would fail verification, which is the point."
                : "Chain complete. The access token expires within the hour, and no key shipped in the app."
        } catch {
            statusMessage = Self.describe(error)
        }
    }

    /// Forgets the App Attest key id and artifact so the next run attests a fresh
    /// key instead of asserting the stored one.
    func reset() {
        guard !isRunning else { return }
        store.reset()
        identity = nil
        tokens.removeAll()
        states = Self.pendingStates
        statusMessage = "Cleared the stored App Attest key id and App Check artifact."
    }

    func claims(for step: GCPAuthStep) -> GCPAuthJWT.Claims? {
        guard let token = tokens[step] else { return nil }
        return GCPAuthJWT.decode(token.value)
    }

    func state(for step: GCPAuthStep) -> GCPAuthStepState {
        states[step] ?? .pending
    }

    private func perform<T>(_ step: GCPAuthStep, _ work: () async throws -> T) async throws -> T {
        set(step, .running)
        do {
            return try await work()
        } catch {
            set(step, .failed(Self.describe(error)))
            throw error
        }
    }

    private func set(_ step: GCPAuthStep, _ state: GCPAuthStepState) {
        states[step] = state
    }

    static func describe(_ error: Error) -> String {
        if let authError = error as? GCPAuthError, let description = authError.errorDescription {
            return description
        }
        return error.localizedDescription
    }
}
