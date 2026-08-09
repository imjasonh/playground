import AuthenticationServices
import CryptoKit
import Foundation
import UIKit

enum GCPAuthNonce {
    /// A fresh random nonce per sign-in attempt. Apple embeds its hash in the
    /// identity token, so a token captured from one attempt cannot be replayed
    /// into another.
    static func random(byteCount: Int = 32) -> String {
        var bytes = [UInt8](repeating: 0, count: byteCount)
        if SecRandomCopyBytes(kSecRandomDefault, byteCount, &bytes) != errSecSuccess {
            bytes = (0..<byteCount).map { _ in UInt8.random(in: UInt8.min...UInt8.max) }
        }
        return bytes.map { String(format: "%02x", $0) }.joined()
    }

    static func sha256Hex(_ input: String) -> String {
        SHA256.hash(data: Data(input.utf8))
            .map { String(format: "%02x", $0) }
            .joined()
    }
}

/// Sign in with Apple, wrapped in `async`/`await`.
///
/// Apple gets the **hashed** nonce (in `request.nonce`) and Firebase later gets
/// the **raw** one, so Firebase can hash it and check the two agree.
///
/// This needs the `com.apple.developer.applesignin` entitlement and the matching
/// App ID capability, which the Playground app does not currently carry — see
/// `GCPAuthConfiguration.appleSignInEnabled`. Without them the request fails at
/// runtime with `ASAuthorizationError.unknown`.
final class GCPAuthAppleSignInController: NSObject {
    struct Credential {
        let identityToken: String
        let rawNonce: String
    }

    private var continuation: CheckedContinuation<Credential, Error>?
    private var rawNonce = ""
    /// `ASAuthorizationController` holds only a weak delegate, so the controller
    /// keeps itself alive for the length of the request.
    private var selfReference: GCPAuthAppleSignInController?

    @MainActor
    func signIn() async throws -> Credential {
        let nonce = GCPAuthNonce.random()
        rawNonce = nonce

        let request = ASAuthorizationAppleIDProvider().createRequest()
        request.requestedScopes = [.fullName, .email]
        request.nonce = GCPAuthNonce.sha256Hex(nonce)

        let controller = ASAuthorizationController(authorizationRequests: [request])
        controller.delegate = self
        controller.presentationContextProvider = self
        selfReference = self

        return try await withCheckedThrowingContinuation { continuation in
            self.continuation = continuation
            controller.performRequests()
        }
    }

    private func finish(with result: Result<Credential, Error>) {
        let pending = continuation
        continuation = nil
        selfReference = nil
        pending?.resume(with: result)
    }
}

extension GCPAuthAppleSignInController: ASAuthorizationControllerDelegate {
    func authorizationController(
        controller: ASAuthorizationController,
        didCompleteWithAuthorization authorization: ASAuthorization
    ) {
        guard
            let credential = authorization.credential as? ASAuthorizationAppleIDCredential,
            let tokenData = credential.identityToken,
            let token = String(data: tokenData, encoding: .utf8)
        else {
            finish(with: .failure(GCPAuthError.missingAppleIdentityToken))
            return
        }
        finish(with: .success(Credential(identityToken: token, rawNonce: rawNonce)))
    }

    func authorizationController(
        controller: ASAuthorizationController,
        didCompleteWithError error: Error
    ) {
        if let authError = error as? ASAuthorizationError, authError.code == .canceled {
            finish(with: .failure(GCPAuthError.appleSignInCancelled))
        } else {
            finish(with: .failure(GCPAuthError.appleSignInFailed(error.localizedDescription)))
        }
    }
}

extension GCPAuthAppleSignInController: ASAuthorizationControllerPresentationContextProviding {
    func presentationAnchor(for controller: ASAuthorizationController) -> ASPresentationAnchor {
        let scenes = UIApplication.shared.connectedScenes.compactMap { $0 as? UIWindowScene }
        let window = scenes
            .flatMap(\.windows)
            .first { $0.isKeyWindow }
        return window ?? scenes.first?.windows.first ?? ASPresentationAnchor()
    }
}
