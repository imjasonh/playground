import SwiftUI

/// Persisted first-run state: install while online, download model, baseline check.
@MainActor
final class OnboardingModel: ObservableObject {
    @Published var baselineRunning = false
    @Published var baselineProgress = ""
    @Published var baselineResult: PlaybookResult?
    @Published var showReadyFlow: Bool

    private let completedKey = "onramp.onboardingCompleted.v1"

    init() {
        showReadyFlow = !UserDefaults.standard.bool(forKey: completedKey)
    }

    var isCompleted: Bool {
        UserDefaults.standard.bool(forKey: completedKey)
    }

    func markCompleted() {
        UserDefaults.standard.set(true, forKey: completedKey)
        showReadyFlow = false
    }

    func runBaseline() async {
        baselineRunning = true
        baselineProgress = "Running a quick online health check…"
        baselineResult = nil
        defer { baselineRunning = false }
        let result = await ConnectivityPlaybookRunner.run(kind: .cantGetOnline) { message in
            await MainActor.run {
                self.baselineProgress = message
            }
        }
        baselineResult = result
        baselineProgress = result.looksOnline
            ? "Baseline looks good — you’re ready for next time you’re offline."
            : "Baseline found a problem even while setting up — fix it now while you’re near a working network."
    }
}

/// Shown once after Apple Intelligence becomes available — journey #1.
struct FirstRunReadyView: View {
    @ObservedObject var onboarding: OnboardingModel
    var onFinished: () -> Void

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 20) {
                Image(systemName: "checkmark.seal.fill")
                    .font(.system(size: 56))
                    .foregroundStyle(.tint)
                    .accessibilityHidden(true)

                Text("You’re set for next time you’re offline")
                    .font(.largeTitle.weight(.bold))

                Text(
                    "Onramp works best when you install it while happily online: Apple Intelligence finishes downloading now, then later — when Wi‑Fi lies — you open Onramp and run Can’t get online."
                )
                .font(.title3)
                .foregroundStyle(.secondary)
                .fixedSize(horizontal: false, vertical: true)

                VStack(alignment: .leading, spacing: 10) {
                    stepRow(number: "1", title: "Model ready", detail: "On-device Foundation Model is available for Chat triage.")
                    stepRow(number: "2", title: "Baseline check", detail: "Run a quick connectivity playbook once while online so you know the app works.")
                    stepRow(number: "3", title: "Later, when stuck", detail: "Open Onramp → Can’t get online. It diagnoses automatically and offers click-to-run next steps.")
                }
                .padding(.vertical, 8)

                HStack(spacing: 12) {
                    Button {
                        Task { await onboarding.runBaseline() }
                    } label: {
                        Text(onboarding.baselineRunning ? "Checking…" : "Run baseline check")
                            .frame(minWidth: 160)
                    }
                    .buttonStyle(.borderedProminent)
                    .controlSize(.large)
                    .disabled(onboarding.baselineRunning)
                    .accessibilityIdentifier("first-run-baseline")

                    Button("I’m ready — go to Playbooks") {
                        onboarding.markCompleted()
                        onFinished()
                    }
                    .buttonStyle(.bordered)
                    .controlSize(.large)
                    .accessibilityIdentifier("first-run-finish")
                }

                if onboarding.baselineRunning || onboarding.baselineResult != nil {
                    VStack(alignment: .leading, spacing: 8) {
                        if onboarding.baselineRunning {
                            HStack(spacing: 8) {
                                ProgressView()
                                    .controlSize(.small)
                                Text(onboarding.baselineProgress)
                                    .foregroundStyle(.secondary)
                            }
                        }
                        if let result = onboarding.baselineResult {
                            TriageReportCard(report: result.triage)
                            if result.looksOnline {
                                Text("Nice — probes succeeded. When you’re offline later, the same playbook will hunt for what broke.")
                                    .foregroundStyle(.secondary)
                            }
                        }
                    }
                }
            }
            .padding(36)
            .frame(maxWidth: 640, alignment: .leading)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .accessibilityIdentifier("first-run-ready")
        .task {
            if onboarding.baselineResult == nil, !onboarding.baselineRunning {
                await onboarding.runBaseline()
            }
        }
    }

    private func stepRow(number: String, title: String, detail: String) -> some View {
        HStack(alignment: .top, spacing: 12) {
            Text(number)
                .font(.headline)
                .frame(width: 28, height: 28)
                .background(Color.accentColor.opacity(0.15))
                .clipShape(Circle())
            VStack(alignment: .leading, spacing: 2) {
                Text(title)
                    .font(.headline)
                Text(detail)
                    .foregroundStyle(.secondary)
            }
        }
    }
}
