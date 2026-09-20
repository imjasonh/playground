import AuthenticationServices
import Foundation

/// Result of `ASAuthorizationAppleIDProvider.getCredentialState`.
enum AppAttestAppleIDState: Equatable, Sendable {
    case authorized
    case revoked
    case notFound
    case unknown
}

/// Looks up whether a stored Sign in with Apple user id is still valid.
protocol AppAttestAppleIDChecking: Sendable {
    func credentialState(forUserID userID: String) async -> AppAttestAppleIDState
}

/// System `ASAuthorizationAppleIDProvider` wrapper. Tests substitute a fake.
struct SystemAppAttestAppleID: AppAttestAppleIDChecking, @unchecked Sendable {
    func credentialState(forUserID userID: String) async -> AppAttestAppleIDState {
        await withCheckedContinuation { continuation in
            ASAuthorizationAppleIDProvider().getCredentialState(forUserID: userID) { state, _ in
                continuation.resume(returning: AppAttestAppleIDState(state))
            }
        }
    }
}

enum AppAttestAppleSignInError: Error, Equatable, LocalizedError {
    case canceled
    case missingUserID
    case failed(String)

    var errorDescription: String? {
        switch self {
        case .canceled:
            return "Sign in canceled."
        case .missingUserID:
            return "Sign in with Apple did not return a user id."
        case .failed(let message):
            return message
        }
    }
}

enum AppAttestAppleSignIn {
    /// Pulls the stable Apple user identifier out of a Sign in with Apple result.
    static func userID(
        from result: Result<ASAuthorization, Error>
    ) -> Result<String, AppAttestAppleSignInError> {
        switch result {
        case .success(let authorization):
            guard let credential = authorization.credential as? ASAuthorizationAppleIDCredential,
                  !credential.user.isEmpty
            else {
                return .failure(.missingUserID)
            }
            return .success(credential.user)
        case .failure(let error):
            if let auth = error as? ASAuthorizationError, auth.code == .canceled {
                return .failure(.canceled)
            }
            return .failure(.failed(error.localizedDescription))
        }
    }
}

private extension AppAttestAppleIDState {
    init(_ state: ASAuthorizationAppleIDProvider.CredentialState) {
        switch state {
        case .authorized:
            self = .authorized
        case .revoked:
            self = .revoked
        case .notFound:
            self = .notFound
        default:
            self = .unknown
        }
    }
}
