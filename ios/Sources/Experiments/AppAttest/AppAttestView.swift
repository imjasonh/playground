import AuthenticationServices
import SwiftUI

/// Attest this device once, then call the Worker that echoes the bound ids.
struct AppAttestView: View {
    @Environment(\.colorScheme) private var colorScheme
    @StateObject private var controller = AppAttestController()

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                availabilityBanner
                identitySection
                actionButtons
                statusLine
                whoamiResults
            }
            .padding()
        }
        .task {
            await controller.refreshAppleIDState()
        }
    }

    private var availabilityBanner: some View {
        Group {
            if controller.isSupported {
                Label("App Attest is available on this device.", systemImage: "checkmark.shield.fill")
                    .foregroundStyle(.green)
            } else if AppAttestEnvironment.isSimulator {
                Label(
                    "App Attest needs a physical iPhone. The Simulator cannot generate a hardware key.",
                    systemImage: "iphone.slash"
                )
                .foregroundStyle(.orange)
            } else {
                Label(
                    "App Attest is not supported on this device.",
                    systemImage: "iphone.slash"
                )
                .foregroundStyle(.orange)
            }
        }
        .font(.subheadline)
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("appAttestAvailabilityBanner")
    }

    @ViewBuilder
    private var identitySection: some View {
        VStack(alignment: .leading, spacing: 12) {
            if controller.isSignedIn {
                LabeledContent("Apple user id", value: controller.userId)
                    .font(.subheadline.monospaced())
                    .textSelection(.enabled)
                    .accessibilityIdentifier("appAttestAppleUserIdValue")
            } else {
                SignInWithAppleButton(.signIn) { request in
                    request.requestedScopes = []
                } onCompletion: { result in
                    let mapped = AppAttestAppleSignIn.userID(from: result)
                    Task { @MainActor in
                        controller.applyAppleSignIn(mapped)
                    }
                }
                .signInWithAppleButtonStyle(colorScheme == .dark ? .white : .black)
                .frame(maxWidth: .infinity, minHeight: 44)
                .accessibilityIdentifier("appAttestSignInButton")
            }

            LabeledContent("Device id", value: controller.deviceId)
                .font(.subheadline.monospaced())
                .textSelection(.enabled)
                .accessibilityIdentifier("appAttestDeviceIdValue")
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private var actionButtons: some View {
        VStack(spacing: 10) {
            Button {
                Task { await controller.register() }
            } label: {
                Label("Register device", systemImage: "checkmark.shield")
                    .frame(maxWidth: .infinity)
            }
            .buttonStyle(.borderedProminent)
            .disabled(controller.isBusy || !controller.isSignedIn)
            .accessibilityIdentifier("appAttestRegisterButton")

            Button {
                Task { await controller.whoami() }
            } label: {
                Label("Call whoami", systemImage: "person.text.rectangle")
                    .frame(maxWidth: .infinity)
            }
            .buttonStyle(.bordered)
            .disabled(controller.isBusy || !controller.hasToken)
            .accessibilityIdentifier("appAttestWhoamiButton")

            if controller.isSignedIn {
                Button {
                    controller.signOut()
                } label: {
                    Label("Sign out", systemImage: "person.crop.circle.badge.minus")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.bordered)
                .disabled(controller.isBusy)
                .accessibilityIdentifier("appAttestSignOutButton")
            }

            Button(role: .destructive) {
                controller.forgetToken()
            } label: {
                Label("Forget token", systemImage: "trash")
                    .frame(maxWidth: .infinity)
            }
            .disabled(!controller.hasToken)
            .accessibilityIdentifier("appAttestForgetButton")
        }
    }

    @ViewBuilder
    private var statusLine: some View {
        Group {
            if controller.statusIsError {
                Label {
                    Text(controller.statusMessage)
                } icon: {
                    Image(systemName: "exclamationmark.triangle.fill")
                }
                .foregroundStyle(.red)
                .accessibilityLabel("Error: \(controller.statusMessage)")
            } else {
                Text(controller.statusMessage)
                    .foregroundStyle(.secondary)
            }
        }
        .font(.body)
        .multilineTextAlignment(.center)
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("appAttestStatusMessage")
    }

    @ViewBuilder
    private var whoamiResults: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Worker response")
                .font(.subheadline.bold())
            if let result = controller.lastWhoAmI {
                VStack(alignment: .leading, spacing: 6) {
                    labeledRow("User id", result.userId)
                    labeledRow("Device id", result.deviceId)
                    labeledRow("Key id", result.keyId)
                    labeledRow("Unattested", result.unattested ? "yes" : "no")
                }
                .font(.body.monospaced())
                .textSelection(.enabled)
                .frame(maxWidth: .infinity, alignment: .leading)
                .padding(12)
                .background(Color.secondary.opacity(0.12), in: RoundedRectangle(cornerRadius: 10))
                .accessibilityIdentifier("appAttestWhoamiResult")
            } else {
                ContentUnavailableView(
                    "No whoami response yet",
                    systemImage: "person.crop.circle.badge.questionmark",
                    description: Text("Sign in with Apple, register this device, then tap Call whoami.")
                )
                .accessibilityIdentifier("appAttestWhoamiEmpty")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private func labeledRow(_ title: String, _ value: String) -> some View {
        VStack(alignment: .leading, spacing: 2) {
            Text(title)
                .font(.caption)
                .foregroundStyle(.secondary)
            Text(value)
        }
    }
}
