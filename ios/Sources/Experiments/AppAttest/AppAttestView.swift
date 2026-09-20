import SwiftUI

/// Attest this device once, then call the Worker that echoes the bound ids.
struct AppAttestView: View {
    @StateObject private var controller = AppAttestController()

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                availabilityBanner
                identityForm
                actionButtons
                Text(controller.statusMessage)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.center)
                    .frame(maxWidth: .infinity)
                    .accessibilityIdentifier("appAttestStatusMessage")
                whoamiResults
                howItWorks
            }
            .padding()
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

    private var identityForm: some View {
        VStack(alignment: .leading, spacing: 12) {
            TextField("user-id", text: $controller.userId)
                .textFieldStyle(.roundedBorder)
                .textInputAutocapitalization(.never)
                .autocorrectionDisabled()
                .accessibilityIdentifier("appAttestUserIdField")

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
            .disabled(controller.isBusy)
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
                    description: Text("Register this device, then tap Call whoami.")
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

    private var howItWorks: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text("How it works")
                .font(.subheadline.bold())
            Text(
                "Register fetches a one-time challenge, hashes user id + device id into App Attest "
                    + "client data, and exchanges the attestation for a JWT. Call whoami sends that "
                    + "token to the app-attest Worker, which returns only the bound ids. The Simulator "
                    + "uses an unattested path that production keeps off."
            )
            .font(.caption)
            .foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }
}
