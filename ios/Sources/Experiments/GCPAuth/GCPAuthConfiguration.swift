import Foundation

/// Everything the credential chain needs to reach a real Firebase + GCP project.
///
/// None of it is a secret, which is the whole point of the design: an iOS app
/// cannot keep one. The Firebase Web API key identifies *which project* you are
/// talking to, not *who you are*, and the workload identity audience is just a
/// resource path. The only thing that proves anything is the Secure Enclave key
/// App Attest creates on the device, and that key can never leave it.
struct GCPAuthConfiguration: Equatable {
    /// Firebase / GCP project id (the string one, e.g. `my-app`). Appears in the
    /// issuer of every Firebase ID token.
    var projectID: String
    /// Numeric project number (e.g. `123456789012`). App Check resource paths and
    /// the workload identity audience use this one, not `projectID`.
    var projectNumber: String
    /// Firebase Web API key (`AIza…`), sent as `?key=` on Firebase REST calls.
    var apiKey: String
    /// Firebase iOS App ID, e.g. `1:123456789012:ios:abc123`.
    var appID: String
    /// Workload identity pool configured to trust Firebase Auth as an OIDC provider.
    var workloadIdentityPoolID: String
    var workloadIdentityProviderID: String
    /// Service account to impersonate after federating. Empty means "use the
    /// federated identity directly", which is the tighter option when the pool's
    /// principal set has been granted exactly what the app needs.
    var serviceAccountEmail: String
    var scopes: [String]
    /// Sign in with Apple needs the `com.apple.developer.applesignin` entitlement
    /// and a matching App ID capability, and that combination requires a one-time
    /// signing bootstrap. Off by default so this experiment stays bootstrap-free;
    /// `docs/ios-gcp-auth-design.md` covers what turning it on costs.
    var appleSignInEnabled: Bool

    static let placeholderProjectNumber = "000000000000"
    static let placeholderAPIKey = "REPLACE_WITH_FIREBASE_WEB_API_KEY"

    /// What the app ships with. In this state the experiment runs against a
    /// canned in-process transport instead of the network.
    static let unconfigured = GCPAuthConfiguration(
        projectID: "replace-with-project-id",
        projectNumber: placeholderProjectNumber,
        apiKey: placeholderAPIKey,
        appID: "1:\(placeholderProjectNumber):ios:0000000000000000",
        workloadIdentityPoolID: "playground-ios-pool",
        workloadIdentityProviderID: "firebase-auth",
        serviceAccountEmail: "",
        scopes: ["https://www.googleapis.com/auth/cloud-platform"],
        appleSignInEnabled: false
    )

    var isConfigured: Bool {
        guard !projectID.isEmpty, !projectID.hasPrefix("replace-with") else { return false }
        guard !projectNumber.isEmpty, projectNumber != Self.placeholderProjectNumber else { return false }
        guard !apiKey.isEmpty, apiKey != Self.placeholderAPIKey else { return false }
        guard !appID.isEmpty, !appID.contains(Self.placeholderProjectNumber) else { return false }
        guard !workloadIdentityPoolID.isEmpty, !workloadIdentityProviderID.isEmpty else { return false }
        return true
    }

    /// Issuer of Firebase ID tokens for this project. The workload identity
    /// provider has to be created with exactly this `--issuer-uri`.
    var firebaseIssuer: String {
        "https://securetoken.google.com/\(projectID)"
    }

    /// STS `audience`, naming the workload identity pool provider that will
    /// accept those Firebase ID tokens.
    var workloadIdentityAudience: String {
        "//iam.googleapis.com/projects/\(projectNumber)"
            + "/locations/global/workloadIdentityPools/\(workloadIdentityPoolID)"
            + "/providers/\(workloadIdentityProviderID)"
    }

    var scopeString: String {
        scopes.joined(separator: " ")
    }

    /// App Check addresses one *app* inside a project.
    var appCheckResource: String {
        "projects/\(projectNumber)/apps/\(appID)"
    }

    /// `signInWithIdp` wants a `requestUri`; Firebase only uses it to match the
    /// authorized domain, and the default hosting domain always qualifies.
    var authorizedDomainURL: String {
        "https://\(projectID).firebaseapp.com"
    }
}

extension GCPAuthConfiguration {
    /// Reads a `GCPAuth` dictionary out of the app's Info.plist when one is
    /// present, so a real project can be wired up without editing source. The
    /// checked-in app has no such key and therefore runs simulated.
    static func fromBundle(_ bundle: Bundle = .main) -> GCPAuthConfiguration {
        guard let raw = bundle.object(forInfoDictionaryKey: "GCPAuth") as? [String: Any] else {
            return .unconfigured
        }
        var configuration = GCPAuthConfiguration.unconfigured
        if let value = raw["ProjectID"] as? String, !value.isEmpty { configuration.projectID = value }
        if let value = raw["ProjectNumber"] as? String, !value.isEmpty { configuration.projectNumber = value }
        if let value = raw["APIKey"] as? String, !value.isEmpty { configuration.apiKey = value }
        if let value = raw["AppID"] as? String, !value.isEmpty { configuration.appID = value }
        if let value = raw["WorkloadIdentityPoolID"] as? String, !value.isEmpty {
            configuration.workloadIdentityPoolID = value
        }
        if let value = raw["WorkloadIdentityProviderID"] as? String, !value.isEmpty {
            configuration.workloadIdentityProviderID = value
        }
        if let value = raw["ServiceAccountEmail"] as? String {
            configuration.serviceAccountEmail = value
        }
        if let value = raw["Scopes"] as? [String], !value.isEmpty { configuration.scopes = value }
        if let value = raw["AppleSignInEnabled"] as? Bool { configuration.appleSignInEnabled = value }
        return configuration
    }
}
